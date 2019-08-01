{-# LANGUAGE StandaloneDeriving #-}

module Main where
import FSM

deriving instance Show a => Show (Set a)
deriving instance (Show a, Show b) => Show (FSM_ext a b)


main = putStrLn "hello Isabelle"
