{-# OPTIONS --universe-polymorphism #-}
module GLFW where

open import Coinduction using ( ♯_ )
open import Data.Unit using ( ⊤ )
open import Data.List
open import IO
import GLFWPrim as GLFWPrim
open import GLFWPrim using ( SessionIODouble ; Step ; Color3 ; color3 ; Double )

initGLFW : IO ⊤
initGLFW =
  ♯ lift GLFWPrim.initGLFW >>
  ♯ return _

quit : IO ⊤
quit =
  ♯ lift GLFWPrim.quit >>
  ♯ return _


drawLights : List (Color3 Double) -> IO ⊤
drawLights l =
  ♯ lift (GLFWPrim.drawLights l) >>
  ♯ return _


stepSessionIO : SessionIODouble -> IO Step
stepSessionIO sid = lift (GLFWPrim.stepSessionIO sid)

