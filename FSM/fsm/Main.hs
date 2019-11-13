{-# LANGUAGE StandaloneDeriving #-}

module Main where
import FSM

deriving instance Show a => Show (Set a)
deriving instance (Show a, Show b) => Show (FSM_ext a b)


main = putStrLn $ show $ maximal_repetition_sets_from_separators m_ex_DR
