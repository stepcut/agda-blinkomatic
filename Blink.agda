{-# OPTIONS --universe-polymorphism --no-termination-check #-}
module Blink where

open import Coinduction -- using ( ♯_ ; ♭_ )
open import Data.Bool using  ( true ; false )
open import Data.Maybe
open import Data.Product
open import Data.List
open import Data.Nat
open import IO
open import Data.Unit using (⊤)
open import GLFW
open import GLFWPrim using ( Step ; step ; clockSession ; SessionIODouble ; Color3 ; color3 ; Double ; primFloatPlus ; primFloatLess ; primFloatMinus )



data LightShow (S A : Set) : Set -> Set1 where
  arr   : forall {B} -> (Maybe A -> Maybe B) -> LightShow S A B
  const : forall {B} -> Maybe B -> LightShow S A B
  gen   : forall {B} -> (S -> Maybe A -> (Maybe B × LightShow S A B)) -> LightShow S A B
  id    : LightShow S A A
  pure  : forall {B} -> (S -> Maybe A -> (Maybe B × LightShow S A B)) -> LightShow S A B

stepLightShow : {A B S : Set} -> LightShow S A B -> S -> Maybe A -> (Maybe B × LightShow S A B)
stepLightShow (arr f)    ds mx' = (f mx' , arr f)
stepLightShow (const mx) ds mx' = ({- mx' *> -} mx , const mx)
stepLightShow (gen f)    ds mx' = f ds mx'
stepLightShow id         ds mx' = (mx' , id)
stepLightShow (pure f)   ds mx' = f ds mx'


_>>>_ : {A B C S : Set} -> LightShow S A B -> LightShow S B C -> LightShow S A C
w1' >>> w2' = gen ( λ ds mx0 →
                         let ( mx1 , w1 ) = stepLightShow w1' ds mx0
                             ( mx2 , w2 ) = stepLightShow w2' ds mx1
                         in ( mx2 , w1 >>> w2 )
                  )


runLightShow : SessionIODouble -> LightShow Double ℕ (List (Color3 Double)) -> IO ⊤
runLightShow s0 l0 =
  ♯ stepSessionIO s0 >>= λ { (step d s) →
  ♯  let ( mb , l ) = stepLightShow l0 d nothing in
   ( maybeDrawLights mb s l {- >> ♯ runLightShow s l -}) }
  where
    maybeDrawLights : Maybe (List (Color3 Double)) -> SessionIODouble -> LightShow Double ℕ (List (Color3 Double)) -> IO ⊤
    maybeDrawLights nothing s l = runLightShow s l
    maybeDrawLights (just colors) s l = ♯ drawLights colors >> ♯ runLightShow s l

timeFrom : forall {A} → Double → LightShow Double A Double
timeFrom t' = pure timeKeeper
  where
  timeKeeper : forall {A} -> Double -> Maybe A -> (Maybe Double × LightShow Double A Double)
  timeKeeper dt _ =
    let t = primFloatPlus t' dt
    in (just t , timeFrom t)

time : forall {A} → LightShow Double A Double
time = timeFrom 0.0

abs : Double -> Double
abs d with primFloatLess d 0.0
... | true  = primFloatMinus 0.0 d
... | false = d

{-
  where
    runLightShow' : Step -> IO ⊤
    runLightShow' (step d s) = return _
-}
{-
with stepLightShow ls clockSession nothing
... | (nothing , ls') = return _
... | (just dt , ls') = return _
-}
t : ℕ × ℕ
t = (zero , zero)

{-
data Wire s e m a b where
    WArr   :: (Either e a -> Either e b) -> Wire s e m a b
    WConst :: Either e b -> Wire s e m a b
    WGen   :: (s -> Either e a -> m (Either e b, Wire s e m a b)) -> Wire s e m a b
    WId    :: Wire s e m a a
    WPure  :: (s -> Either e a -> (Either e b, Wire s e m a b)) -> Wire s e m a b

type LightShow = (Fractional t, HasTime t s) => Wire s () Identity Int [GL.Color3 GL.GLfloat]
-}

