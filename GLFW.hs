{-# LANGUAGE DeriveFunctor #-}
module GLFW
    ( initGLFW
    , quit
    , drawLights
    , Session
    , SessionIODouble
    , Step(..)
    , stepSessionIO
    , clockSession
    ) where

import Control.Arrow (second)
import Control.Monad (forM_, forever)
import Control.Monad.Trans (MonadIO(liftIO))
import Data.Time.Clock (UTCTime, diffUTCTime, getCurrentTime)
import qualified Graphics.Rendering.OpenGL as GL
import Graphics.Rendering.OpenGL (($=))
import qualified Graphics.UI.GLFW as GLFW

initGLFW :: IO ()
initGLFW =
    do initGLFW'
       return ()

initGLFW' :: IO Bool
initGLFW' =
  do r <- GLFW.initialize
     case r of
       False -> return False
       True ->
           do r <- GLFW.openWindow GLFW.defaultDisplayOptions
                   { GLFW.displayOptions_numRedBits   = 8
                   , GLFW.displayOptions_numGreenBits = 8
                   , GLFW.displayOptions_numBlueBits  = 8
                   , GLFW.displayOptions_numDepthBits = 1
                   , GLFW.displayOptions_width        = 640
                   , GLFW.displayOptions_height       = 480
                   }
              case r of
                False -> return False
                True ->
                    do GLFW.setWindowSizeCallback $ resize
                       -- Use `$=` for assigning to GL values, `get` to read them.
                       -- These functions basically hide IORefs.

                       GL.depthFunc $= Just GL.Less
                       return True

-- | Resize the viewport and set the projection matrix
resize :: Int -> Int -> IO ()
resize w h = do
  -- These are all analogous to the standard OpenGL functions
  GL.viewport     $= (GL.Position 0 0, GL.Size (fromIntegral w) (fromIntegral h))
  GL.matrixMode   $= GL.Projection
  GL.loadIdentity
  GL.perspective  45 (fromIntegral w / fromIntegral h) 1 100
  GL.matrixMode   $= GL.Modelview 0

-- | Close the window and terminate GLFW
quit :: IO ()
quit = GLFW.closeWindow >> GLFW.terminate

-- | This will print and clear the OpenGL errors
printErrors = GL.get GL.errors >>= mapM_ print

drawLights :: [GL.Color3 Double] -> IO ()
drawLights colors = do
  -- Again, the functions in GL almost all map to standard OpenGL functions
  GL.clear [GL.ColorBuffer, GL.DepthBuffer]

  GL.loadIdentity
  GL.translate $ GL.Vector3 (-10) 0 (-50 :: GL.GLfloat)
--  GL.scale 10 10 (1 :: GL.GLfloat)
  GL.renderPrimitive GL.Quads $
    forM_ (zip [0 .. (fromIntegral (length colors)) - 1 ] colors) $ \(l, c) -> do
      let c'  = let (GL.Color3 r g b) = c in (GL.Color3 (realToFrac r) (realToFrac g) (realToFrac b))
      GL.color  (c' :: GL.Color3 GL.GLfloat)
--      do print (c, c')
      forM_ [(0,0), (1,0), (1,1), (0, 1)] $ \(x, y) ->
          let vtx = GL.Vertex3 (x + (l * 2)) y 0 :: GL.Vertex3 GL.GLfloat
          in GL.vertex vtx

  printErrors

  GL.flush
  GLFW.swapBuffers


{-

-- | This state delta type denotes time deltas.  This is necessary for
-- most FRP applications.


instance (Monoid s, Real t) => HasTime t (Timed t s) where
    dtime (Timed dt _) = dt

instance (Monoid s, Num t) => Monoid (Timed t s) where
    mempty = Timed 0 mempty

    mappend (Timed dt1 ds1) (Timed dt2 ds2) =
        let dt = dt1 + dt2
            ds = ds1 <> ds2
        in dt `seq` ds `seq` Timed dt ds
-}



-- clockSession :: (MonadIO m) => Session m (s -> Timed NominalDiffTime s)

-- clockSession :: (MonadIO m) => Session m (s -> Timed NominalDiffTime s)
{-

-}

data Timed t s = Timed t s
    deriving (Eq, Functor,
              Ord, Read, Show)

newtype Session m s =
    Session {
      stepSession :: m (s, Session m s)
    }
    deriving (Functor)

type SessionIODouble = Session IO Double

data Step = Step Double SessionIODouble

stepSessionIO :: SessionIODouble -> IO Step
stepSessionIO = fmap toStep . stepSession
    where
      toStep (d, s) = Step d s



clockSession :: SessionIODouble
clockSession = fmap realToFrac clockSession_

clockSession_ = Session $
    do t0 <- getCurrentTime
       return (0, loop t0)

loop t' = Session $
    do t <- getCurrentTime
       let dt = diffUTCTime t t'
       dt `seq` return (dt, loop t)

