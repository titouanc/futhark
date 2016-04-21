{-# LANGUAGE TypeFamilies #-}
-- | Trying to do some stuff to memory blocks
module Futhark.MemoryBlockDerping
       (memoryBlockDerping)
       where

import Futhark.Representation.ExplicitMemory

memoryBlockDerping :: Prog -> IO ()
memoryBlockDerping = mapM_ lookAtFunction . progFunctions

lookAtFunction :: FunDec -> IO ()
lookAtFunction (FunDec fname rettype params body) = do
  putStrLn $ "This is the of name: " ++ nameToString fname
  putStrLn $ "  and return type: " ++ pretty rettype
  putStrLn $ "  and parameters: " ++ pretty params
  let Body () bnds res = body
  putStrLn $ "The function returns this: " ++ pretty res
  putStrLn "Which is computed by these bindings: "
  mapM_ lookAtBinding bnds
  where lookAtBinding (Let pat () e) = do
          putStrLn $ "The binding with pattern: " ++ pretty pat
          putStrLn $ "And corresponding expression:\n" ++
                     unlines (map ("  "++) $ lines $ pretty e)
