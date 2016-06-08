{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Playground for work on merging memory blocks
module Futhark.MemoryBlockMerging
       ( memoryBlockMerging )
       where

import qualified Data.Map.Strict as Map
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

import Futhark.Representation.ExplicitMemory as ExplicitMemory
import Futhark.Representation.AST.Attributes.Names as Names

import Futhark.Tools -- intraproceduraltransformation
import Futhark.Pass -- simplepass
import Futhark.MonadFreshNames -- MonadFreshNames

memoryBlockMerging :: Prog -> IO ()
memoryBlockMerging = mapM_ lookAtFunction . progFunctions


lookAtFunction :: FunDef -> IO ()
lookAtFunction (FunDef entry fname rettype params body) = do
  let Body () bnds res = body
  let allocs = findAllocs bnds Map.empty
--  let storedVars = findStoredVars' bnds allocs -- old
  let storedVars = findStoredVars bnds allocs Map.empty -- new
--  let lastUseTable = findLastUse bnds storedVars -- old
  let lastUseTable = findLastUse' bnds storedVars Map.empty -- new
  let conv = invert lastUseTable
-- man burde faktisk checke for res i luTab og smide i free listen
  let (newBnds, freeList) = f conv (bnds, Map.empty)
--  putStrLn "Old bindings:"
--  mapM_ lookAtBinding bnds
--  mapM_ lamePrint0 bnds
--  putStrLn "\n\nConverted bindings:"
  mapM_ lookAtBinding newBnds

  putStrLn "--Allocs:"
  mapM_ lamePrint $ Map.toList allocs
  putStrLn "\n--Stored vars:"
  mapM_ lamePrint2 $ Map.toList storedVars
  putStrLn "\n--Last use table:"
  mapM_ lamePrint2 $ Map.toList lastUseTable
  putStrLn "\n--Freelist:"
  mapM_ lamePrintFreeList $ Map.toList freeList

--  mapM_ onlyMapKernels bnds
  where lookAtBinding (Let pat () e) = do
          putStrLn $ "The binding with pattern: " ++ pretty pat
          putStrLn $ "And corresponding expression:\n" ++
                     unlines (map ("  "++) $ lines $ pretty e)

onlyMapKernels :: Binding -> IO ()
onlyMapKernels bnd
  | (Let pat att exp) <- bnd,
--    Op (Inner (MapKernel cs w index ispace inps rettype kBody)) <- exp = do
    Op (Inner (MapKernel cs w index ispace ((KernelInput inParam inArray inIndices):_) rettype kBody)) <- exp = do
      putStrLn $ "The binding has pattern: " ++ pretty pat
      putStrLn $ "And corresponding exp: " ++ pretty exp
      putStrLn $ "With Kernel input: "
      putStrLn $ "Width: " ++ pretty w
      putStrLn $ "Index: " ++ pretty index
      putStrLn $ "Ispace: " ++ pretty ispace
      putStrLn $ "Input params: " ++ pretty inParam
      putStrLn $ "Input array: " ++ pretty inArray
      putStrLn $ "Input indices: " ++ pretty inIndices
--      putStrLn $ "With kernel input arrays: " ++ unlines (map ("  "++) $ lines $ pretty inps)
  | (Let pat att exp) <- bnd = do
      putStrLn $ "Don't care about this binding"

lamePrint0 :: Binding -> IO ()
lamePrint0 (Let (Pattern _ ((PatElem patVar _ _):_)) att exp)  =
  let vars = HS.toList $ freeInExp exp in
  mapM_ (\x -> putStrLn ("pat: " ++ (pretty patVar) ++ " var: " ++ (pretty x))) vars


lamePrint :: (VName, (SubExp, Space)) -> IO ()
lamePrint (name, (size, space)) =
  putStrLn ("Mem.name: " ++ (pretty name) ++ " size: " ++ (pretty size) ++ " space: " ++ (help space))
  where help sp =
          case sp of
            DefaultSpace -> "DefaultSpace"
            Space x -> x

lamePrint2 :: (VName, (VName, SubExp, Space)) -> IO ()
lamePrint2 (val, (mem, sz, sp)) =
  putStrLn ("Mem.name: " ++ (pretty mem) ++ " Val.name: " ++ (pretty val))

lamePrintFreeList :: ((SubExp, Space), [VName]) -> IO ()
lamePrintFreeList ((sz, sp), xs) = do
  putStrLn ("Size: " ++ (pretty sz) ++ " Space: " ++ (help sp))
  putStrLn ("Mems: " ++ unlines (map ("  "++) $ lines $ pretty xs))
  where help sp =
          case sp of
            DefaultSpace -> "DefaultSpace"
            Space x -> x

-- The function that does the actual substitution/aliasing/merging
f :: Map.Map VName [(VName, SubExp, Space)]
     -> ([Binding], Map.Map (SubExp, Space) [VName])
     -> ([Binding], Map.Map (SubExp, Space) [VName])
f _ ([], freeList) = ([], freeList)
f luTab ((Let pat att exp):bnds, freeList)
  | Op (Inner (MapKernel cs w index ispace inps rettype kBody)) <- exp,
    Body kAtt kBnds kRes <- kBody,
    Pattern _ valElems <- pat =
      let (kBnds', _) = f luTab (kBnds, Map.empty) in -- start mapkernel with empty list
      let kBody' = Body kAtt kBnds' kRes in
      let exp' = Op (Inner (MapKernel cs w index ispace inps rettype kBody')) in
      let freeList' = foldl (flHelper luTab) freeList inps in -- her bliver kernel inputs tilføjet free listen
      let freeList'' = toFreeList valElems luTab freeList' in -- her bliver 696 og 698 tilføjet free listen
      let (bnds', freeList''') = f luTab (bnds, freeList'') in
      ((Let pat att exp'):bnds', freeList''')
  | Op (Alloc size space) <- exp,
    Just (freeList', x) <- fromFreeList size space freeList,
    Pattern _ valElems <- pat,
    freeList'' <- toFreeList valElems luTab freeList' =
      let (bnds', freeList''') = f luTab (bnds, freeList'') in
      (Let pat att (PrimOp (SubExp (Var x))):bnds', freeList''')
  | Pattern _ valElems <- pat,
    freeList' <- toFreeList valElems luTab freeList =
      let (bnds', freeList'') = f luTab (bnds, freeList') in
      ((Let pat att exp):bnds', freeList'')
  where flHelper luTab freeList (KernelInput (Param p _) arr idx) =
          case Map.lookup p luTab of
            Just xs -> foldl flHelper' freeList xs
            Nothing -> freeList
        flHelper' map (mem, size, space) =
          case Map.lookup (size, space) map of
            Just xs ->
              if elem mem xs
              then map
              else Map.insertWith (++) (size, space) [mem] map
            Nothing ->
              Map.insertWith (++) (size, space) [mem] map

-- Inverts a map from key=mem to key=lu_var
invert :: Map.Map VName (VName, SubExp, Space)
          -> Map.Map VName [(VName, SubExp, Space)]
invert map =
  foldl f Map.empty $ Map.toList map
  where f map (mem, (var, sz, sp)) =
          Map.insertWith (++) var [(mem, sz, sp)] map

--
{-
kernelToFreeList :: [KernelInput]
                    -> Map.Map VName [(VName, SubExp, Space)]
                    -> Map.Map (SubExp, Space) [VName]
                    -> Map.Map (SubExp, Space) [VName]
kernelToFreeList inps lastUseMap freeList =
  foldl (kernelToFreeListHelper lastUseMap) freeList inps

kernelToFreeListHelper :: Map.Map VName [(VName, SubExp, Space)]
                          -> Map.Map (SubExp, Space) [VName]
                          -> KernelInput
                          -> Map.Map (SubExp, Space) [VName]
kernelToFreeListHelper lastUseMap freeList (KernelInput _ _ _) =
  case Map.lookup p lastUseMap of
    Just xs -> foldl f freeList xs
    Nothing -> freeList
  where f freeList (mem, size, space) =
          case Map.lookup (size, space) freeList of
            Just xs ->
              if elem mem xs
              then freeList
              else Map.insertWith (++) (size, space) [mem] freeList
            Nothing -> freeList
-}
--
{-
resToFreeList :: [SubExp]
                  -> Map.Map VName [(VName, SubExp, Space)]
                  -> Map.Map (SubExp, Space) [VName]
                  -> Map.Map (SubExp, Space) [VName]
resToFreeList vars luTab freeList =
  foldl (\freeList var -> resToFreeListHelper var luTab freeList) freeList vars

resToFreeListHelper :: SubExp
                  -> Map.Map VName [(VName, SubExp, Space)]
                  -> Map.Map (SubExp, Space) [VName]
                  -> Map.Map (SubExp, Space) [VName]
resToFreeListHelper var luTab freeList =
  case var of
    Var elemIdName ->
      case Map.lookup elemIdName luTab of
        Just xs -> foldl f freeList xs
        Nothing -> freeList
    Constant _ -> freeList -- doesnt care about constants
  where f map (mem, size, space) =
          case Map.lookup (size, space) freeList of
            Just xs ->
              if elem mem xs
              then freeList
              else Map.insertWith (++) (size, space) [mem] freeList
            Nothing ->
              Map.insertWith (++) (size, space) [mem] freeList
-}
-- Inserts a memory block into the front of the free list of a given key.
-- Now takes an list of PatElems instead
toFreeList :: [PatElem]
                  -> Map.Map VName [(VName, SubExp, Space)]
                  -> Map.Map (SubExp, Space) [VName]
                  -> Map.Map (SubExp, Space) [VName]
toFreeList vars luTab freeList =
  foldl (\freeList var -> toFreeListHelper var luTab freeList) freeList vars

toFreeListHelper :: PatElem
                  -> Map.Map VName [(VName, SubExp, Space)]
                  -> Map.Map (SubExp, Space) [VName]
                  -> Map.Map (SubExp, Space) [VName]
toFreeListHelper (PatElem elemIdName _ _) luTab freeList =
  case Map.lookup elemIdName luTab of
    Just xs -> foldl f freeList xs
    Nothing -> freeList
  where f map (mem, size, space) =
          case Map.lookup (size, space) map of
            Just xs ->
              if elem mem xs
              then map
              else Map.insertWith (++) (size, space) [mem] map
            Nothing ->
              Map.insertWith (++) (size, space) [mem] map

{- -- old version
toFreeList :: VName
                  -> Map.Map VName [(VName, SubExp, Space)]
                  -> Map.Map (SubExp, Space) [VName]
                  -> Map.Map (SubExp, Space) [VName]
toFreeList var luTab freeList =
  case Map.lookup var luTab of
    Just xs -> foldl f freeList xs
    Nothing -> freeList
  where f map (mem, size, space) =
          Map.insertWith (++) (size, space) [mem] freeList
-}

-- Extracts a memory block (if any) with the given size. Returns the updated map
-- and a 'free' memory block. Always chooses the first element at a given size.
fromFreeList :: SubExp
                   -> Space
                   -> Map.Map (SubExp, Space) [VName]
                   -> Maybe (Map.Map (SubExp, Space) [VName], VName)
fromFreeList size space freeList =
  case Map.lookup (size, space) freeList of
    Just (x:[]) -> Just (Map.delete (size, space) freeList, x)
    Just (x:xs) -> Just (Map.insert (size, space) xs freeList, x)
    Nothing     -> Nothing

-- 3)
-- Traverses the AST and checks for each expression in a binding if any of the
-- variables are stored in a memory block. Ultimately, we get information about
-- when a memory blocks is used for the last time.
{-
findLastUse :: [Binding]
               -> Map.Map VName (VName, SubExp, Space)
               -> Map.Map VName (VName, SubExp, Space)
findLastUse bnds memTab =
  foldl (\luTab (Let pat _ e) ->
           foldl (lastUse' memTab pat) luTab (HS.toList $ freeInExp e))
  Map.empty bnds
  where lastUse' memTab (Pattern _ valueE) luTab freeVar =
          case valueE of -- if pat is a tuple we only look at the first value, could be done more elegantly
            (PatElem var _ _ ):vs ->
              case Map.lookup freeVar memTab of
                Just (mem, sz, sp) -> Map.insert mem (var, sz, sp) luTab
                Nothing -> luTab
            _ -> luTab
-}

-- remember to check for all values in pattern
findLastUse' :: [Binding]
                -> Map.Map VName (VName, SubExp, Space)
                -> Map.Map VName (VName, SubExp, Space)
                -> Map.Map VName (VName, SubExp, Space)
findLastUse' [] _ lastUseMap = lastUseMap
findLastUse' ((Let pat _ exp):bnds) storedVarsMap lastUseMap
  | Op (Inner (MapKernel _ _ _ _ kInps _ kBody)) <- exp,
    Pattern _ valElems <- pat,
    Body _ kBnds kRes <- kBody =
    let lastUseMap' = foldl (opHelper storedVarsMap) lastUseMap kInps in
    let lastUseMap'' = findLastUse' kBnds storedVarsMap lastUseMap' in
    let pairs = zipper valElems kRes in -- zipping pattern elements with results
    let lastUseMapFi = foldl (resHelper storedVarsMap) lastUseMap'' pairs in
    findLastUse' bnds storedVarsMap lastUseMapFi
  where opHelper storedVarsMap lastUseMap (KernelInput (Param p _) arr _) =
          case Map.lookup arr storedVarsMap of
            Just (mem, sz, sp) -> Map.insert mem (p, sz, sp) lastUseMap
            Nothing -> lastUseMap
        resHelper storedVars lastUseMap (pat, res) =
          case Map.lookup res storedVarsMap of
            Just (mem, sz, sp) -> Map.insert mem (pat, sz, sp) lastUseMap
            Nothing -> lastUseMap
findLastUse' ((Let (Pattern _ valElems) _ exp):bnds) storedVarsMap lastUseMap =
  let freeVars = HS.toList $ freeInExp exp in
  let lastUseMap' = foldl (helper storedVarsMap valElems) lastUseMap freeVars in
  findLastUse' bnds storedVarsMap lastUseMap'
  where helper storedVarsMap ((PatElem var _ _):_) lastUseMap e =
          case Map.lookup e storedVarsMap of
            Just (mem, sz, sp) -> Map.insert mem (var, sz, sp) lastUseMap
            Nothing -> lastUseMap

-- Modified the zipWith function to handle this specific pattern matching
zipper _ [] = []
zipper [] _ = []
zipper ((PatElem pVar _ _):xs) ((Var kVar):ys) = (pVar, kVar) : zipper xs ys
zipper (_:xs) (_:ys) = zipper xs ys



-- 2)
-- Locates the identifiers stored in the memoryblocks found in 1)
{-
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
-}

-- not very elegant, but that was what I could come up with at the moment
findStoredVars :: [Binding]
                  -> Map.Map VName (SubExp, Space)
                  -> Map.Map VName (VName, SubExp, Space)
                  -> Map.Map VName (VName, SubExp, Space)
findStoredVars [] _ varMap = varMap
findStoredVars ((Let pat _ exp):bnds) memMap varMap
-- if expression is mapkernel - traverse it
  | Op (Inner (MapKernel _ _ _ _ _ _ kBody)) <- exp,
    Body _ kBnds _ <- kBody,
    Pattern _ vals <- pat =
      let varMap'  = foldl (getArrayMem memMap) varMap vals in
      let varMap'' = findStoredVars kBnds memMap varMap' in
      findStoredVars bnds memMap varMap''
-- if pattern is ArrayMem
  | Pattern _ vals <- pat =
    let varMap' = foldl (getArrayMem memMap) varMap vals in
    findStoredVars bnds memMap varMap'
  where getArrayMem memMap varMap v =
          case v of
            (PatElem valName _ (ArrayMem _ _ _ memName _)) ->
              case Map.lookup memName memMap of
                Just (sz, sp) ->
                  Map.insert valName (memName, sz, sp) varMap
                Nothing ->
                  varMap
            _ -> varMap

{-
-- 1)
-- Locates the allocations (alloc() calls) and stores them in a map
findAllocs :: [Binding] -> Map.Map VName (SubExp, Space)
findAllocs bnds =
  foldl mapAlloc Map.empty bnds
  where mapAlloc map (Let pat _ e) =
          case pat of
            Pattern _ [PatElem memName _ (MemMem sz sp)] ->
              Map.insert memName (sz, sp) map
            _ -> map
-}

-- This version takes mapkernels into account
findAllocs :: [Binding]
               -> Map.Map VName (SubExp, Space)
               -> Map.Map VName (SubExp, Space)
findAllocs [] map = map
findAllocs ((Let pat _ exp):bnds) map
  | Pattern _ [PatElem memName _ (MemMem sz sp)] <- pat =
      findAllocs bnds (Map.insert memName (sz, sp) map)
  | Op (Inner (MapKernel _ _ _ _ _ _ kBody)) <- exp,
    Body _ kBnds _ <- kBody,
    kAllocs <- findAllocs kBnds map =
      findAllocs bnds kAllocs
  | Pattern _ _ <- pat =
      findAllocs bnds map
