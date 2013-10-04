module Main where

open import Coinduction using ( ♯_ )
open import Data.List
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Nat using ( ℕ )
open import Data.Unit using ( ⊤ )
open import GLFW
open import GLFWPrim using ( clockSession ; Color3 ; color3 ; Double ; primSin )
open import IO
open import Blink

onewhitesquare : LightShow Double ℕ (List (Color3 Double))
onewhitesquare = const (just ((color3 1.0 1.0 1.0) ∷ []))

sinefade  : LightShow Double ℕ (List (Color3 Double))
sinefade =
  time >>> arr timeToColor
  where
  timeToColor : Maybe Double -> Maybe (List (Color3 Double))
  timeToColor nothing  = nothing
  timeToColor (just t) = 
    let c = abs (primSin t) in  just (color3 c c c ∷ [])

main′ : IO ⊤
main′ =
  ♯ initGLFW >>
  ♯ (♯ runLightShow clockSession sinefade >>
  ♯    quit)


main = run main′
