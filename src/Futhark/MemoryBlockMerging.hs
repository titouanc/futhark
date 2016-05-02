{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-} -- woah
-- | Playground for work on merging memory blocks
module Futhark.MemoryBlockMerging
       (memoryBlockMerging)
       where

-- loading Futhark modules
import           Futhark.Representation.ExplicitMemory as ExplicitMemory
import           Futhark.Representation.AST.Attributes.Names as Names

-- loading Data module and map qualified
import           Data.Map (Map)
import qualified Data.Map as Map -- otherwise ambiguity

-- importing hashsets
import qualified Data.HashSet as HS

-- importing hashmaps because freeInExp returns a hashmap (Names is a hashmap)
import qualified Data.HashMap.Lazy as HM


-- function that does magic from original MemoryBlockMering module
memoryBlockMerging :: Prog -> IO ()
memoryBlockMerging = (mapM_ lookAtFunction) . progFunctions



-- function that prints the result of use-maps creation
lookAtFunction :: FunDec -> IO ()
lookAtFunction (FunDec fname rettype params body) = do

  let Body () bnds res = body

  let primaryMap = storeMemBlock body
  let firstUseMap = firstUse body primaryMap
  let lastUseMap = lastUse body primaryMap
  let unionedUse = Map.unionWith (\(f1, _, sz) (l1, _, _) -> (f1, l1, sz)) firstUseMap lastUseMap

  putStrLn "Unioned use list:"
  mapM_ printMap (Map.toList unionedUse)

  putStrLn "\n"
  putStrLn "Size to mem list:"
  let sztomem = sizeToMem unionedUse
  mapM_ printSizeToMem (Map.toList sztomem)


-- function that prints size-to-mem map
printSizeToMem :: (String, [(String, String, String)]) -> IO ()
printSizeToMem (sz, xs) =
                putStrLn $ sz ++ " -- " ++ unlines (map (" "++) $ lines $ pretty xs)


-- function that creates size-to-mem map
sizeToMem :: Map.Map String (String, String, String) -> Map.Map String [(String, String, String)]
sizeToMem memToInfo =
  foldl (\newMap (mem, (fu, lu, sz)) -> Map.insertWith (++) sz [(mem, fu, lu)] newMap) Map.empty $ Map.toList memToInfo


-- function that prints first-use/last-use/unioned-use maps
printMap :: (String, (String, String, String)) -> IO ()
printMap (mem, (fu, lu, sz)) =
  putStrLn ("(" ++ mem ++ ", (" ++ fu ++ ", " ++ lu ++ ", " ++ sz ++ "))")


-- function that creates first use map | (mem, (fu, "", size))
firstUse :: Body -> Map.Map VName (VName, String) -> Map.Map String (String, String, String)
firstUse (Body _ bnds res) primaryMap =
  foldr (\(Let pat _ e) useMap -> foldr (firstUse' primaryMap pat) useMap (HS.toList $ freeInExp e)) Map.empty bnds
  
-- helper function to firstUse
firstUse' :: Map.Map VName (VName, String) ->
              Pattern ->
              VName ->
              Map.Map String (String, String, String) ->
              Map.Map String (String, String, String)
firstUse' primaryMap (Pattern _ [PatElem name _ _]) varName dataMap =
  case Map.lookup varName primaryMap of
    Just (mem, size) -> Map.insert (pretty mem) ((pretty name), "", size) dataMap
    Nothing -> dataMap
    

-- function that creates last use map | (mem, (lu, "", size))
lastUse :: Body -> Map.Map VName (VName, String) -> Map.Map String (String, String, String)
lastUse (Body _ bnds res) primaryMap =
  foldl (\useMap (Let pat _ e) -> foldl (lastUse' primaryMap pat) useMap (HS.toList $ freeInExp e)) Map.empty bnds

-- helper function to lastUse
lastUse' :: Map.Map VName (VName, String) ->
             Pattern ->
             Map.Map String (String, String, String) ->
             VName ->
             Map.Map String (String, String, String)
lastUse' primaryMap (Pattern _ [PatElem name _ _]) dataMap varName =
  case Map.lookup varName primaryMap of
    Just (mem, size) -> Map.insert (pretty mem) (pretty name, "", size) dataMap
    Nothing -> dataMap


-- memory block annotations | (var, (mem, size))
storeMemBlock :: Body -> Map.Map VName (VName, String)
storeMemBlock (Body _ bnds res) =
  foldl mapMemBlock Map.empty bnds
  where mapMemBlock dataMap (Let pat () e) = do
          case getBlockName pat of
            Just (var, mem, size) -> Map.insert var (mem, pretty size) dataMap
            Nothing -> dataMap
        getBlockName (Pattern _ [PatElem var _ (ArrayMem _ (Shape [size]) _ mem _)]) =
          Just (var, mem, size)
        getBlockName _ =
          Nothing












-- Code leftovers from earlier version of module

{-
  putStrLn $ "This is the of name: " ++ nameToString fname
  putStrLn $ "  and return type: " ++ pretty rettype
  putStrLn $ "  and parameters: " ++ pretty params
-}

{-
  putStrLn $ "The function returns this: " ++ pretty res
  putStrLn "Which is computed by these bindings: "
-}

{-
  putStrLn "First use list: "
  mapM_ printMap (Map.toList firstUseMap)
  putStrLn "Last use list: "
  mapM_ printMap (Map.toList lastUseMap)
-}

{-
--  mapM_ printBinding (Map.toList test)
--  mapM_ lookAtBinding bnds
-}

{-
  let sizetest = storeSize body
  mapM_ printSize (Map.toList sizetest)
-}

{-

  where lookAtBinding (Let pat () e) = do
          putStrLn $ "The binding with pattern: " ++ pretty pat
          putStrLn $ "And corresponding expression:\n" ++
                     unlines (map ("  "++) $ lines $ pretty e)
          let xs = HS.toList (freeInExp e)
          putStrLn $ "vars (exp): " ++ unlines (map (" "++) $ lines $ pretty xs)
-}



{-
-- just a test function to see, if the map is created correct
printBinding :: (VName, VName) -> IO ()
printBinding (var, block) =
  putStrLn ("var: " ++ (pretty var) ++ "\n" ++ "block: " ++ (pretty block))
-}

