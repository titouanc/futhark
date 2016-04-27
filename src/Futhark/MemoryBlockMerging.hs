{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-} -- woah
-- | Playground for work on merging memory blocks
module Futhark.MemoryBlockMerging
       (memoryBlockMerging)
       where

import Futhark.Representation.ExplicitMemory as ExplicitMemory

import qualified Data.Map as Map -- otherwise ambiguity

import Data.Map (Map)
import qualified Data.Map as Map -- otherwise ambiguity

import Data.Char

import Futhark.Representation.AST.Attributes.Names as Names
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM


memoryBlockMerging :: Prog -> IO ()
memoryBlockMerging = (mapM_ lookAtFunction) . progFunctions

lookAtFunction :: FunDec -> IO ()
lookAtFunction (FunDec fname rettype params body) = do

  putStrLn $ "This is the function of name: " ++ nameToString fname
  putStrLn $ "  and return type: " ++ pretty rettype
  putStrLn $ "  and parameters: " ++ pretty params

{-
  putStrLn $ "This is the of name: " ++ nameToString fname
  putStrLn $ "  and return type: " ++ pretty rettype
  putStrLn $ "  and parameters: " ++ pretty params
-}

  let Body () bnds res = body
{-
  putStrLn $ "The function returns this: " ++ pretty res
  putStrLn "Which is computed by these bindings: "

  mapM_ lookAtBinding bnds
  let test = storeMemBlock body
  mapM_ printBinding (Map.toList test)
-- storeMemBlock body should go here
-- storeMemBlock body
-- foldl mapMemBlock Map.empty bnds
-}

  let primaryMap = storeMemBlock body
  let firstUseMap = firstUse body primaryMap
  let lastUseMap = lastUse body primaryMap
  let unionedUse = Map.unionWith (\(f1, _) (l1, _) -> (f1, l1)) firstUseMap lastUseMap
  putStrLn "First use list: "
  mapM_ printMap (Map.toList firstUseMap)
  putStrLn "Last use list: "
  mapM_ printMap (Map.toList lastUseMap)
  putStrLn "Unioned use list: "
  mapM_ printMap (Map.toList unionedUse)
--  mapM_ printBinding (Map.toList test)
--  mapM_ lookAtBinding bnds
  where lookAtBinding (Let pat () e) = do
          putStrLn $ "The binding with pattern: " ++ pretty pat
          putStrLn $ "And corresponding expression:\n" ++
                     unlines (map ("  "++) $ lines $ pretty e)


-- just a test function to see, if the map is created correct
printBinding :: (VName, VName) -> IO ()
printBinding (var, block) =
  putStrLn ("var: " ++ (pretty var) ++ "\n" ++ "block: " ++ (pretty block))
          let xs = HS.toList (freeInExp e)
          putStrLn $ "vars (exp): " ++ unlines (map (" "++) $ lines $ pretty xs)

printMap :: (String, (String, String)) -> IO ()
printMap (mem, (fu, lu)) =
  putStrLn ("(" ++ mem ++ ", (" ++ fu ++ ", " ++ lu ++ "))")

firstUse :: Body -> Map.Map VName VName -> Map.Map String (String, String)
firstUse (Body _ bnds res) primaryMap =
  foldr (\(Let pat _ e) useMap -> foldr (firstUse' primaryMap pat) useMap (HS.toList $ freeInExp e)) Map.empty bnds

firstUse' :: Map.Map VName VName -> Pattern -> VName -> Map.Map String (String, String) -> Map.Map String (String, String)
firstUse' primaryMap (Pattern _ [PatElem name _ _]) varName dataMap =
  case Map.lookup varName primaryMap of -- check if it's a block-annotated var
    Just mem -> Map.insert (pretty mem) ((pretty name), "") dataMap
    Nothing -> dataMap

{--- should correspond to the double-foldl-lambda-function above
  foldl (func primaryMap) Map.empty bnds
  where func primaryMap useMap (Let pat _ e) = do
          let xs = HS.toList (freeInExp e)
          foldl (use primaryMap) useMap xs
-}

lastUse :: Body -> Map.Map VName VName -> Map.Map String (String, String)
lastUse (Body _ bnds res) primaryMap =
  foldl (\useMap (Let pat _ e) -> foldl (lastUse' primaryMap pat) useMap (HS.toList $ freeInExp e)) Map.empty bnds

lastUse' :: Map.Map VName VName -> Pattern -> Map.Map String (String, String) -> VName -> Map.Map String (String, String)
lastUse' primaryMap (Pattern _ [PatElem name _ _]) dataMap varName =
  case Map.lookup varName primaryMap of -- check if it's a block-annotated var
    Just mem -> Map.insert (pretty mem) ((pretty name), "") dataMap
    Nothing -> dataMap

{-
lastUse :: Body -> Map.Map VName VName -> Map.Map String (String, String)
lastUse (Body _ bnds res) primaryMap = do
  foldr (func primaryMap) Map.empty bnds
  where func primaryMap useMap (Let pat _ e) = do
          let xs = HS.toList (freeInExp e)
          foldr (use primaryMap) useMap xs
-}

-- creates a map with all memory block allocations (ugly sheit)
storeMemBlock :: Body -> Map.Map VName VName
storeMemBlock (Body _ bnds res) =
  foldl mapMemBlock Map.empty bnds
  where mapMemBlock dataMap (Let pat () e) = do
          case getBlockName pat of
            Just (var, block) -> Map.insert var block dataMap
            Nothing -> dataMap
        getBlockName (Pattern _ [PatElem name _ (ArrayMem _ _ _ blockName _)]) =
          Just (name, blockName)
        getBlockName _ =
          Nothing


-- functions used in storeMemBlock

{-
-- just a test function to see, if the map is created correct
printBinding :: (VName, VName) -> IO ()
printBinding (var, block) =
  putStrLn ("var: " ++ (pretty var) ++ "\n" ++ "block: " ++ (pretty block))
-}




-- functions used in storeMemBlock
{-
getBlockName (Let (Pattern _ [PatElem name _ (ArrayMem _ _ _ blockName _)]) _ e) =
  Just (name, blockName)
getBlockName _ =
  Nothing

-- cannot type annotate Let??
mapMemBlock :: Map.Map String String -> (Let pat () e) -> Map.Map String String
mapMemBlock dataMap letBinding = do
  case getBlockName letBinding of
    Just (var, block) -> Map.insert var block dataMap
    Nothing -> dataMap

mapMemBlock' :: Map.Map String String -> Maybe (String, String) -> Map.Map String String
mapMemBlock' dataMap maybeValue = do
  case maybeValue of
    Just (var, block) -> Map.insert var block dataMap
    Nothing -> dataMap
-}

-- For each binding, store all variables in a global map. If the local variables
-- for that identifier is not in the map, they are stored in a local map.
-- For each binding store a tuple in a list, consisting of the identifier and a
-- map (containing the vars that has not been seen before).


