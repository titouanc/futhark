{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-} -- woah
-- | Playground for work on merging memory blocks
module Futhark.MemoryBlockMerging
       (memoryBlockMerging)
       where

import Futhark.Representation.ExplicitMemory as ExplicitMemory
import Data.Map (Map)
import qualified Data.Map as Map -- otherwise ambiguity

import Futhark.Representation.AST.Attributes.Names as Names
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

memoryBlockMerging :: Prog -> IO ()
memoryBlockMerging = (mapM_ lookAtFunction) . progFunctions

lookAtFunction :: FunDec -> IO ()
lookAtFunction (FunDec fname rettype params body) = do
  putStrLn $ "This is the of name: " ++ nameToString fname
  putStrLn $ "  and return type: " ++ pretty rettype
  putStrLn $ "  and parameters: " ++ pretty params
  putStrLn $ "This is where John come in"
  let Body () bnds res = body
  putStrLn $ "The function returns this: " ++ pretty res
  putStrLn "Which is computed by these bindings: "
  mapM_ lookAtBinding bnds
--  let test = storeMemBlock body
--  mapM_ printBinding (Map.toList test)
  where lookAtBinding (Let pat () e) = do
          putStrLn $ "The binding with pattern: " ++ pretty pat
          putStrLn $ "And corresponding expression:\n" ++
                     unlines (map ("  "++) $ lines $ pretty e)
          let xs = HS.toList (freeInExp e)
          putStrLn $ "vars (exp): " ++ unlines (map (" "++) $ lines $ pretty xs)

-- just a test function to see, if the map is created correct
printBinding :: (VName, VName) -> IO ()
printBinding (var, block) =
  putStrLn ("var: " ++ (pretty var) ++ "\n" ++ "block: " ++ (pretty block))

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


