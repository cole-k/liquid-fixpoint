{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified ParserTests
import qualified QeTests
import qualified ShareMapTests
import qualified SimplifyTests
import qualified SimplifyKVarTests
import qualified InterpretTests
import qualified UndoANFTests
import Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ ParserTests.tests
  , QeTests.tests
  , ShareMapTests.tests
  , SimplifyTests.tests
  , SimplifyKVarTests.tests
  , InterpretTests.tests
  , UndoANFTests.tests
  ]
