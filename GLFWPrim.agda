{-# OPTIONS --universe-polymorphism #-}
module GLFWPrim where

open import Foreign.Haskell
open import IO.Primitive
open import Data.List
open import Data.Bool

{-# IMPORT IO.FFI #-}
{-# IMPORT GLFW #-}
{-# IMPORT Graphics.Rendering.OpenGL #-}

data Color3 (A  : Set) : Set where
  color3 : A -> A -> A -> Color3 A
{-# COMPILED_DATA Color3 Graphics.Rendering.OpenGL.Color3 Graphics.Rendering.OpenGL.Color3 #-}

postulate
  Double     : Set
  SessionIODouble : Set

{-# BUILTIN FLOAT Double #-}
{-# COMPILED_TYPE Double Double #-}
{-# COMPILED_TYPE SessionIODouble GLFW.SessionIODouble #-}

data Step : Set where
  step : Double -> SessionIODouble -> Step
{-# COMPILED_DATA Step GLFW.Step GLFW.Step #-}

postulate
  initGLFW   : IO Unit
  quit       : IO Unit
  drawLights : List (Color3 Double) -> IO Unit
  stepSessionIO : SessionIODouble -> IO Step
  clockSession : SessionIODouble

{-# COMPILED_TYPE IO IO.FFI.AgdaIO #-}
{-# COMPILED initGLFW GLFW.initGLFW #-}
{-# COMPILED drawLights GLFW.drawLights #-}
{-# COMPILED quit GLFW.quit #-}
{-# COMPILED stepSessionIO GLFW.stepSessionIO #-}
{-# COMPILED clockSession GLFW.clockSession #-}

primitive
  primFloatPlus  : Double -> Double -> Double
  primFloatMinus : Double -> Double -> Double
  primFloatTimes : Double -> Double -> Double
  primFloatDiv   : Double -> Double -> Double
  primFloatLess  : Double -> Double -> Bool
  primSin        : Double -> Double

