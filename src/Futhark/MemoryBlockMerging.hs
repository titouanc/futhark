{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-} -- woah
-- | Playground for work on merging memory blocks
module Futhark.MemoryBlockMerging
       (memoryBlockMerging)
       where

import Futhark.Representation.ExplicitMemory as ExplicitMemory
import Data.Map (Map)
import qualified Data.Map as Map -- otherwise ambiguity

import qualified Data.List as List

import Futhark.Representation.AST.Attributes.Names as Names
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

-- Creating a new datatype for ease of handling memory block information
data MemInfo = MemInfo { memoryBlock :: VName
                       , lastUseVariable :: VName
                       , blockSize :: SubExp
                       }

-- Accessor functions
getMem :: MemInfo -> VName
getMem (MemInfo memoryBlock _ _) = memoryBlock

getVar :: MemInfo -> VName
getVar (MemInfo _ lastUseVariable _) = lastUseVariable

getSize :: MemInfo -> SubExp
getSize (MemInfo _ _ blockSize) = blockSize

getAll :: MemInfo -> String
getAll (MemInfo mem var sz) =
  (pretty mem) ++ " " ++
  (pretty var) ++ " " ++
  (pretty sz)

memoryBlockMerging :: Prog -> IO ()
memoryBlockMerging = mapM_ lookAtFunction . progFunctions

lookAtFunction :: FunDec -> IO ()
lookAtFunction (FunDec fname rettype params body) = do
  putStrLn $ "This is the function of name: " ++ nameToString fname
  putStrLn $ "  and return type: " ++ pretty rettype
  putStrLn $ "  and parameters: " ++ pretty params
  let Body () bnds res = body
  putStrLn $ "The function returns this: " ++ pretty res
  putStrLn "Which is computed by these bindings: "

-- playground
  let memTab = findAllocs bnds
  let lastUseTab = findLastUse bnds memTab
  let newBnds = f lastUseTab Map.empty bnds
  let newMemTab = findAllocs newBnds
  putStrLn "Old binds"
  printAllocs memTab
  putStrLn "New binds"
  printAllocs newMemTab

{-
  putStrLn "Memory allocations:"
  printAllocs memTab
  putStrLn "\nLast use table:"
  mapM_ printLuTab (Map.toList lastUseTab)
-}
-- playground
{-
  mapM_ lookAtBinding bnds
  putStrLn "\n\n\nConverted bnds:"
  mapM_ lookAtBinding newBnds
-}
  where lookAtBinding (Let pat () e) = do
          putStrLn $ "The binding with pattern: " ++ pretty pat
          putStrLn $ "And corresponding expression:\n" ++
                     unlines (map ("  "++) $ lines $ pretty e)


printAllocs :: Map.Map VName MemInfo -> IO ()
printAllocs map =
  mapM_ (\(memk, (MemInfo memv var sz)) ->
           putStrLn (
            "mem: " ++ (pretty memv) ++
            "\nvar: " ++ (pretty var) ++
            "\nsize: " ++ (pretty sz) ++ "\n"))
  (Map.toList map)


printLuTab :: (VName, [MemInfo]) -> IO ()
printLuTab (sz, meminfo) = do
  putStrLn ("lu: " ++ (pretty sz))
  mapM_ (\x -> putStrLn ("MemInfo: " ++ (getAll x) ++ "\n")) meminfo








f :: Map.Map VName [MemInfo] -> Map.Map SubExp [MemInfo] -> [Binding] -> [Binding]
f _ _ [] = []
f luTab freeList ((Let pat att exp):bnds)
  | (Pattern conElems valElems) <- pat,
    [PatElem elemIdName elemBind elemAttr] <- valElems,
    (ArrayMem primType (Shape [size]) u memName idxFun) <- elemAttr =
--
    case extractFreeList size freeList of
-- vs af træ på papir
      (newFL, Just y) -> do
        let newElemAttr = (ArrayMem primType (Shape [size]) u (getMem y) idxFun)
        let newValElems = ([PatElem elemIdName elemBind newElemAttr])
        let newPat      = (Pattern conElems newValElems)
        let newLuTab = updateLuTab luTab elemIdName (getMem y) memName
        -- check if variable is a last use variable
        case Map.lookup elemIdName luTab of
          Just (x:[]) -> do
            let newFL = insertFreeList freeList (getSize x) x
            (Let newPat att exp):(f newLuTab newFL bnds)
          Just (x:xs) -> do
            let newFL = foldl
                  (\map inf -> insertFreeList map (getSize inf) inf) freeList (x:xs)
            (Let newPat att exp):(f newLuTab newFL bnds)
          Nothing     -> (Let newPat att exp):(f luTab newFL bnds)
-- hs af træ på papir
      (_, Nothing) -> do
        -- check if variable is a last use variable
        case Map.lookup elemIdName luTab of
          Just (x:[]) -> do
            let newFL = insertFreeList freeList (getSize x) x
            (Let pat att exp):(f luTab newFL bnds)
          Just (x:xs) -> do
            let newFL = foldl
                  (\map inf -> insertFreeList map (getSize inf) inf) freeList (x:xs)
            (Let pat att exp):(f luTab newFL bnds)
          Nothing     -> (Let pat att exp):(f luTab freeList bnds)
-- If binding is not an allocation. We still need to check if var is last use.
  | (Pattern conElems valElems) <- pat,
    [PatElem elemIdName elemBind elemAttr] <- valElems =
      case Map.lookup elemIdName luTab of
        Just (x:[]) -> do
          let newFL = insertFreeList freeList (getSize x) x
          (Let pat att exp):(f luTab newFL bnds)
        Just (x:xs) -> do
          let newFL = foldl
                (\map inf -> insertFreeList map (getSize inf) inf) freeList (x:xs)
          (Let pat att exp):(f luTab newFL bnds)
        Nothing ->
          (Let pat att exp):(f luTab freeList bnds)
--
f _ _ _ = []


-- Inserts a memory block in the free list. Inserts in the front of the list.
insertFreeList :: Map.Map SubExp [MemInfo] -> SubExp -> MemInfo -> Map.Map SubExp [MemInfo]
insertFreeList freeList size mem =
  Map.insertWith (++) size [mem] freeList

-- Extracts a memory block (if any) with the given size. Returns the updated map
-- and a 'free' memory block. Always chooses the first element at a given size.
extractFreeList :: SubExp -> Map.Map SubExp [MemInfo] -> (Map.Map SubExp [MemInfo], Maybe MemInfo)
extractFreeList size freeList =
  case Map.lookup size freeList of
    Just (x:[]) -> (Map.delete size freeList, Just x)
    Just (x:xs) -> (Map.insert size xs freeList, Just x)
    Nothing     -> (freeList, Nothing)

-- Updates the last use table/map. This function is called if a memory block is
-- reused, and thus gets a new point of last use.
updateLuTab :: Map.Map VName [MemInfo] -> VName -> VName -> VName
               -> Map.Map VName [MemInfo]
updateLuTab luTab oldLuVar newLuVar upMem = do
  case Map.lookup oldLuVar luTab of
    Just xs ->
      case List.partition (\x -> (getMem x) == upMem) xs of
        ([], ys) -> luTab
        ([MemInfo mem var size], ys) -> do
          let tmp = Map.insert oldLuVar ys luTab
          Map.insertWith (++) newLuVar [MemInfo mem newLuVar size] tmp
        (_, []) -> luTab -- this should cause an error
    Nothing -> luTab

-- Traverses the AST and checks for each expression in a binding, if any of the
-- variables are stored in a memory block. Ultimately, we get information about
-- when a memory blocks is used for the last time.
findLastUse :: [Binding] -> Map.Map VName MemInfo -> Map.Map VName [MemInfo]
findLastUse bnds memTab =
  foldl (\luTab (Let pat _ e) ->
           foldl (lastUse' memTab pat) luTab (HS.toList $ freeInExp e))
  Map.empty bnds
  where lastUse' memTab (Pattern _ [PatElem var _ _ ]) luTab freeVar =
          case Map.lookup freeVar memTab of
            Just x -> Map.insertWith (++) (getVar x) [x] luTab
            Nothing -> luTab

-- Traversing the AST and stores the memory block number, identifier and size,
-- for each allocation in the body. The key is the identifier.
findAllocs :: [Binding] -> Map.Map VName MemInfo
findAllocs bnds =
  foldl mapMemBlock Map.empty bnds
  where mapMemBlock map (Let pat _ e) = do
          case pat of
            (Pattern _ [PatElem var _ (ArrayMem _ (Shape [size]) _ mem _)]) ->
              Map.insert var (MemInfo mem var size) map
            _ -> map
