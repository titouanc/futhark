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

lookAtFunction :: FunDef -> IO ()
lookAtFunction (FunDef entry fname rettype params body) = do
{-
  putStrLn $ "This is the function of name: " ++ nameToString fname
  putStrLn $ "  and return type: " ++ pretty rettype
  putStrLn $ "  and parameters: " ++ pretty params
  putStrLn $ "The function returns this: " ++ pretty res
  putStrLn "Which is computed by these bindings: "
-}

-- playground
  let Body () bnds res = body
  let allocs = findAllocs bnds
  let storedVars = findStoredVars' bnds allocs
  let lastUseTable = findLastUse bnds storedVars
  let conv = invert lastUseTable
  let newBnds = f conv Map.empty bnds

  {-
  putStrLn "Memory allocations:"
  printAllocs memTab
-}

--  putStrLn "\nLast use table:"
--  mapM_ printLuTab (Map.toList conv)


--  test bnds

--  putStrLn "\nAlloc types: "
--  mapM_ test bnds

-- playground

  mapM_ lookAtBinding bnds
  putStrLn "\n\n\nConverted bnds:"
  mapM_ lookAtBinding newBnds

  where lookAtBinding (Let pat () e) = do
          putStrLn $ "The binding with pattern: " ++ pretty pat
          putStrLn $ "And corresponding expression:\n" ++
                     unlines (map ("  "++) $ lines $ pretty e)


test :: [Binding] -> IO ()
test bnds = do
  mapM_ print bnds
  where print (Let pat () e) =
          case (pat, e) of
            (Pattern _ [PatElem elemIdName _ (MemMem size space)], Op (Alloc sz sp)) ->
              putStrLn ("var: " ++ (pretty elemIdName) ++
                        "\n-- MemMem: " ++ " size: " ++ (pretty size) ++ " space: " ++ (pretty space) ++
                        "\n-- Alloc: " ++ "size: " ++ (pretty sz) ++ " space: " ++ (pretty sp))
            (Pattern _ [PatElem elemIdName _ _], _) ->
              putStrLn ("var: " ++ (pretty elemIdName))
{-
  | Op (Alloc sz sp) <- exp,
    (Pattern _ valElems) <- pat,
    [PatElem elemIdName _ elemAttr] <- valElems,
    MemMem size space <- elemAttr = do
-}



invert :: Map.Map VName (VName, SubExp, Space) -> Map.Map VName [(VName, SubExp, Space)]
invert map = do
  let tmp = Map.toList map
  foldl f Map.empty tmp
  where f map (mem, (var, sz, sp)) =
          Map.insertWith (++) var [(mem, sz, sp)] map


printAllocs :: Map.Map VName MemInfo -> IO ()
printAllocs map =
  mapM_ (\(memk, (MemInfo memv var sz)) ->
           putStrLn (
            "mem: " ++ (pretty memv) ++
            "\nvar: " ++ (pretty var) ++
            "\nsize: " ++ (pretty sz) ++ "\n"))
  (Map.toList map)


printLuTab :: (VName, [(VName, SubExp, Space)]) -> IO ()
printLuTab (var, memInfo) = do
  putStrLn ("var: " ++ (pretty var))
  mapM_ (\(mem, sz, sp) -> putStrLn ("mem: " ++ (pretty mem) ++ "\n" ++
                                     "size: " ++ (pretty sz) ++ "\n" ++
                                     "space: " ++ (pretty sp) ++ "\n")) memInfo




f :: Map.Map VName [(VName, SubExp, Space)] -> Map.Map (SubExp, Space) [VName] -> [Binding] -> [Binding]
f _ _ [] = []
f luTab freeList ((Let pat att exp):bnds)
--  | Pattern conElems [PatElem elemIdName _ (ArrayMem _ (Shape [sz]) _ _ _)] <- pat =
 -- burde være valid
  | Op (Alloc size space) <- exp,
    Just (freeList', x) <- extractFreeList size space freeList,
    Pattern _ [PatElem elemIdName _ _] <- pat,
    freeList'' <- insertFreeList elemIdName luTab freeList' = do
      Let pat att (PrimOp (SubExp (Var x))):(f luTab freeList'' bnds)
-- If binding is not an allocation. We still need to check if var is last use.
  | Pattern conElems [PatElem elemIdName _ _] <- pat,
    freeList' <- insertFreeList elemIdName luTab freeList = do
      (Let pat att exp):(f luTab freeList' bnds)



 -- These two functions should just be rewritten
-- Inserts a memory block in the free list. Inserts in the front of the list.
insertFreeList :: VName
                  -> Map.Map VName [(VName, SubExp, Space)]
                  -> Map.Map (SubExp, Space) [VName]
                  -> Map.Map (SubExp, Space) [VName]
insertFreeList var luTab freeList =
  case Map.lookup var luTab of
    Just xs -> foldl f freeList xs
    Nothing -> freeList
  where f map (mem, size, space) =
          Map.insertWith (++) (size, space) [mem] freeList

-- Extracts a memory block (if any) with the given size. Returns the updated map
-- and a 'free' memory block. Always chooses the first element at a given size.
extractFreeList :: SubExp
                   -> Space
                   -> Map.Map (SubExp, Space) [VName]
                   -> Maybe (Map.Map (SubExp, Space) [VName], VName)
extractFreeList size space freeList =
  case Map.lookup (size, space) freeList of
    Just (x:[]) -> Just (Map.delete (size, space) freeList, x)
    Just (x:xs) -> Just (Map.insert (size, space) xs freeList, x)
    Nothing     -> Nothing



{-
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
-}

-- 3)
-- Traverses the AST and checks for each expression in a binding if any of the
-- variables are stored in a memory block. Ultimately, we get information about
-- when a memory blocks is used for the last time.
findLastUse :: [Binding]
               -> Map.Map VName (VName, SubExp, Space)
               -> Map.Map VName (VName, SubExp, Space)
findLastUse bnds memTab =
  foldl (\luTab (Let pat _ e) ->
           foldl (lastUse' memTab pat) luTab (HS.toList $ freeInExp e))
  Map.empty bnds
  where lastUse' memTab (Pattern _ [PatElem var _ _ ]) luTab freeVar =
          case Map.lookup freeVar memTab of
            Just (mem, sz, sp) -> Map.insert mem (var, sz, sp) luTab
            Nothing -> luTab


-- 2)
findStoredVars' :: [Binding]
                   -> Map.Map VName (SubExp, Space)
                   -> Map.Map VName (VName, SubExp, Space)
findStoredVars' bnds allocMap =
  foldl (mapMemBlock allocMap) Map.empty bnds
  where mapMemBlock allocMap map (Let pat _ e) =
          case pat of
            Pattern _ [PatElem elemIdName _ (ArrayMem _ _ _ mem _)] ->
              case Map.lookup mem allocMap of
                Just (sz, sp) -> Map.insert elemIdName (mem, sz, sp) map
                Nothing -> map -- should not be possible - unallocated mem.block
            _ -> map

-- 1)
findAllocs :: [Binding] -> Map.Map VName (SubExp, Space)
findAllocs bnds =
  foldl mapAlloc Map.empty bnds
  where mapAlloc map (Let pat _ e) =
          case pat of
            Pattern _ [PatElem memName _ (MemMem sz sp)] ->
              Map.insert memName (sz, sp) map
            _ -> map

{-
-- Traversing the AST and stores the memory block number, identifier and size,
-- for each identifier stored in a memory block. The identifier is key.
findStoredVars :: [Binding] -> Map.Map VName VName
findStoredVars bnds =
  foldl mapMemBlock Map.empty bnds
  where mapMemBlock map (Let pat _ e) =
          case pat of
            (Pattern _ [PatElem elemIdName _ (ArrayMem _ _ _ mem _)]) ->
              Map.insert elemIdName mem map
            _ -> map
-}
