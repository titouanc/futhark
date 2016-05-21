{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Playground for work on merging memory blocks
module Futhark.Pass.MemoryBlockMerging
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

memoryBlockMerging :: Pass ExplicitMemory ExplicitMemory
memoryBlockMerging =
  simplePass
  "memoryblock merging"
  "Memoryblock merging" $
  intraproceduralTransformation transformFunDec

transformFunDec :: MonadFreshNames m => FunDec -> m FunDec
transformFunDec fundec =
  let body' = transformBody $ funDecBody fundec in
  return fundec { funDecBody = body' }

transformBody :: Body -> Body
transformBody (Body att bnds res) =
  let allocs = findAllocs bnds in
  let storedVars = findStoredVars' bnds allocs in
  let lastUseTable = findLastUse bnds storedVars in
  let conv = invert lastUseTable in
  let bnds' = f conv Map.empty bnds in
  Body att bnds' res

-- The function that does the actual substitution/aliasing/merging
f :: Map.Map VName [(VName, SubExp, Space)]
     -> Map.Map (SubExp, Space) [VName] -> [Binding] -> [Binding]
f _ _ [] = []
f luTab freeList ((Let pat att exp):bnds)
  | Op (Alloc size space) <- exp,
    Just (freeList', x) <- fromFreeList size space freeList,
    Pattern _ [PatElem elemIdName _ _] <- pat,
    freeList'' <- toFreeList elemIdName luTab freeList' =
      Let pat att (PrimOp (SubExp (Var x))):(f luTab freeList'' bnds)
  | Pattern conElems [PatElem elemIdName _ _] <- pat,
    freeList' <- toFreeList elemIdName luTab freeList =
      (Let pat att exp):(f luTab freeList' bnds)

-- Inverts a map from key=mem to key=lu_var
invert :: Map.Map VName (VName, SubExp, Space)
          -> Map.Map VName [(VName, SubExp, Space)]
invert map =
  let tmp = Map.toList map in
  foldl f Map.empty tmp
  where f map (mem, (var, sz, sp)) =
          Map.insertWith (++) var [(mem, sz, sp)] map

-- Inserts a memory block into the front of the free list of a given key.
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
-- Locates the identifiers stored in the memoryblocks found in 1)
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
-- Locates the allocations (alloc() calls) and stores them in a map
findAllocs :: [Binding] -> Map.Map VName (SubExp, Space)
findAllocs bnds =
  foldl mapAlloc Map.empty bnds
  where mapAlloc map (Let pat _ e) =
          case pat of
            Pattern _ [PatElem memName _ (MemMem sz sp)] ->
              Map.insert memName (sz, sp) map
            _ -> map
