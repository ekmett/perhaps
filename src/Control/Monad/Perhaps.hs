{-# language CPP #-}
{-# language DefaultSignatures #-}
{-# language DeriveTraversable #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language Safe #-}
{-# language StandaloneDeriving #-}
{-# language TypeFamilies #-}
{-# language UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (c) Edward Kmett 2018
-- License     :  BSD3
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  stable
-- Portability :  portable
--
-----------------------------------------------------------------------------

module Control.Monad.Perhaps
  ( 
  -- * Maybe with an undisclosed error
    Perhaps(..)
  , believe
  , mayhap
  -- * Transformer
  , PerhapsT(..)
  -- * Class
  , MonadPerhaps(..)
  -- * Combinators
  , mapPerhapsT
  , liftCallCC
  , liftCatch
  , liftListen
  , liftPass
  ) where

import Control.Applicative
import Control.Exception (Exception(..), throw)
import Control.Monad as Monad
import Control.Monad.Trans
import Control.Monad.Cont.Class
#if MIN_VERSION_base(4,9,0)
import Control.Monad.Fail as MonadFail
#endif
import Control.Monad.Fix (MonadFix(mfix))
import Control.Monad.RWS as Lazy
import Control.Monad.RWS.Strict as Strict
import Control.Monad.Reader
import Control.Monad.Signatures
import Control.Monad.State as Lazy
import Control.Monad.State.Strict as Strict
import Control.Monad.Trans.Identity (IdentityT(..))
import Control.Monad.Writer as Lazy
import Control.Monad.Writer.Strict as Strict
import Control.Monad.Zip (MonadZip(munzip, mzipWith))
import Data.Void

--------------------------------------------------------------------------------
-- * Perhaps
--------------------------------------------------------------------------------

data Perhaps a
  = Can a
  | Can't Void
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

instance Semigroup a => Semigroup (Perhaps a) where
  Can a   <> Can b   = Can (a <> b)
  Can't _ <> Can b   = Can b
  Can a   <> Can't _ = Can a
  Can't e <> Can't _ = Can't e
  {-# inlinable (<>) #-}

instance Semigroup a => Monoid (Perhaps a) where
  mempty = empty 
  {-# inlinable mempty #-}
  mappend = (<>)
  {-# inlinable mappend #-}

instance Applicative Perhaps where
  pure = Can
  {-# inlinable pure #-}
  Can f <*> Can a = Can (f a)
  Can't e <*> _ = Can't e
  _ <*> Can't e = Can't e
  {-# inlinable (<*>) #-}

instance Alternative Perhaps where
  empty = Can't (error "empty")
  {-# inlinable empty #-}
  a@Can{} <|> _ = a
  _ <|> a@Can{} = a
  e <|> _       = e
  {-# inlinable (<|>) #-}

instance Monad Perhaps where
  return = pure
  {-# inlinable return #-}

  Can a >>= f = f a
  Can't e >>= _ = Can't e
  {-# inlinable (>>=) #-}

#if MIN_VERSION_base(4,9,0)
  fail = MonadFail.fail
  {-# inlinable fail #-}

instance MonadFail Perhaps where
#endif
  fail e = Can't (error e)
  {-# inlinable fail #-}

instance MonadPlus Perhaps where
  mplus = (<|>)
  {-# inlinable mplus #-}
  mzero = empty
  {-# inlinable mzero #-}


instance MonadFix Perhaps where
  mfix f = a where a = f (believe a)
  {-# inlinable mfix #-}

instance MonadZip Perhaps where
  munzip (Can (a,b)) = (Can a, Can b)
  munzip (Can't e) = (Can't e, Can't e)
  {-# inlinable munzip #-}
  mzipWith f (Can a) (Can b) = Can (f a b)
  mzipWith _ (Can't e) _ = Can't e
  mzipWith _ _ (Can't e) = Can't e
  {-# inlinable mzipWith #-}

-- | partial!
believe :: Perhaps a -> a
believe (Can a) = a
believe (Can't e) = absurd e
{-# inlinable believe #-}

mayhap :: Perhaps a -> Maybe a
mayhap (Can a) = Just a
mayhap (Can't _) = Nothing
{-# inlinable mayhap #-}

--------------------------------------------------------------------------------
-- * PerhapsT
--------------------------------------------------------------------------------

newtype PerhapsT m a = PerhapsT { runPerhapsT :: m (Perhaps a) }
  deriving (Functor, Foldable, Traversable)

deriving instance Eq (m (Perhaps a)) => Eq (PerhapsT m a)
deriving instance Ord (m (Perhaps a)) => Ord (PerhapsT m a)
deriving instance Show (m (Perhaps a)) => Show (PerhapsT m a)
deriving instance Read (m (Perhaps a)) => Read (PerhapsT m a)

instance Monad m => Applicative (PerhapsT m) where
  pure = PerhapsT . pure . pure
  {-# inlinable pure #-}
  PerhapsT mf <*> PerhapsT ma = PerhapsT $ mf >>= \f0 -> case f0 of
    Can't e -> pure $ Can't e
    Can f -> fmap f <$> ma
  {-# inlinable (<*>) #-}

instance Monad m => Alternative (PerhapsT m) where
  empty = PerhapsT (pure empty)
  {-# inlinable empty #-}
  PerhapsT ma <|> PerhapsT mb = PerhapsT $ ma >>= \a0 -> case a0 of
    a@Can{} -> pure a
    e@Can't{} -> mb >>= \b0 -> case b0 of
      b@Can{} -> pure b
      Can't{} -> pure e
  {-# inlinable (<|>) #-}

instance Monad m => Monad (PerhapsT m) where
  return = pure
  {-# inlinable return #-}

  PerhapsT ma >>= f = PerhapsT $ ma >>= \a0 -> case a0 of
    Can a   -> runPerhapsT (f a)
    Can't e -> pure (Can't e)
  {-# inlinable (>>=) #-}

#if MIN_VERSION_base(4,9,0)
  fail = MonadFail.fail
  {-# inlinable fail #-}

instance Monad m => MonadFail (PerhapsT m) where
#endif
  fail = PerhapsT . pure . MonadFail.fail
  {-# inlinable fail #-}

instance Monad m => MonadPlus (PerhapsT m) where
  mzero = empty
  {-# inlinable mzero #-}
  mplus = (<|>)
  {-# inlinable mplus #-}

instance MonadZip m => MonadZip (PerhapsT m) where
  mzipWith f (PerhapsT a) (PerhapsT b) = PerhapsT $ mzipWith (liftA2 f) a b
  {-# inlinable mzipWith #-}
  munzip m = (fmap fst m, fmap snd m)
  {-# inlinable munzip #-}

instance MonadFix m => MonadFix (PerhapsT m) where
  mfix f = PerhapsT $ mfix (runPerhapsT . f . believe)
  {-# inlinable mfix #-}

instance MonadTrans PerhapsT where
  lift = PerhapsT . fmap Can
  {-# inlinable lift #-}

instance MonadIO m => MonadIO (PerhapsT m) where
  liftIO = lift . liftIO
  {-# inlinable liftIO #-}

instance MonadState s m => MonadState s (PerhapsT m) where
  get = lift get
  {-# inlinable get #-}
  put = lift . put
  {-# inlinable put #-}
  state = lift . state
  {-# inlinable state #-}

instance MonadWriter w m => MonadWriter w (PerhapsT m) where
  tell = lift . tell
  {-# inlinable tell #-}
  writer = lift . writer
  {-# inlinable writer #-}
  listen = liftListen listen
  {-# inlinable listen #-}
  pass = liftPass pass
  {-# inlinable pass #-}

instance MonadCont m => MonadCont (PerhapsT m) where
  callCC = liftCallCC callCC
  {-# inlinable callCC #-}

instance MonadReader r m => MonadReader r (PerhapsT m) where
  ask = lift ask
  {-# inlinable ask #-}
  reader = lift . reader
  {-# inlinable reader #-}
  local = mapPerhapsT . local
  {-# inlinable local #-}

-- | Lift a @callCC@ operation to the new monad.
liftCallCC :: CallCC m (Perhaps a) (Perhaps b) -> CallCC (PerhapsT m) a b
liftCallCC k f =
  PerhapsT $ k $ \ c -> runPerhapsT (f (PerhapsT . c . Can))
{-# inlinable liftCallCC #-}

-- | Lift a @catchE@ operation to the new monad.
liftCatch :: Catch e m (Perhaps a) -> Catch e (PerhapsT m) a
liftCatch f m h = PerhapsT $ f (runPerhapsT m) (runPerhapsT . h)
{-# inlinable liftCatch #-}

-- | Lift a @listen@ operation to the new monad.
liftListen :: Monad m => Listen w m (Perhaps a) -> Listen w (PerhapsT m) a
liftListen l = mapPerhapsT $ \ m -> do
  (a, w) <- l m
  return $! fmap (\ r -> (r, w)) a
{-# inlinable liftListen #-}

-- | Lift a @pass@ operation to the new monad.
liftPass :: Monad m => Pass w m (Perhaps a) -> Pass w (PerhapsT m) a
liftPass p = mapPerhapsT $ \ m -> p $ do
  a <- m
  return $! case a of
    Can't e -> (Can't e, id)
    Can (v, f) -> (Can v, f)
{-# inlinable liftPass #-}

-- | Transform the computation inside a @PerhapsT@.
--
-- * @'runPerhapsT' ('mapPerhapsT' f m) = f ('runPerhapsT' m)@
mapPerhapsT :: (m (Perhaps a) -> n (Perhaps b)) -> PerhapsT m a -> PerhapsT n b
mapPerhapsT f = PerhapsT . f . runPerhapsT
{-# INLINE mapPerhapsT #-}

--------------------------------------------------------------------------------
-- * MonadPerhaps
--------------------------------------------------------------------------------

class MonadPlus m => MonadPerhaps m where
  -- | This is a monad homomorphism
  perhaps :: Perhaps a -> m a
  default perhaps :: (m ~ t n, MonadTrans t, MonadPerhaps n) => Perhaps a -> m a
  perhaps = lift . perhaps

  -- | Fail with an exception as an excuse instead of just a string.
  excuse :: Exception e => e -> m a
  excuse = perhaps . Can't . throw 

instance MonadPerhaps Perhaps where
  perhaps = id
  {-# inlinable perhaps #-}

instance Monad m => MonadPerhaps (PerhapsT m) where
  perhaps = PerhapsT . pure
  {-# inlinable perhaps #-}
  
instance MonadPerhaps m => MonadPerhaps (Lazy.StateT s m)
instance MonadPerhaps m => MonadPerhaps (Strict.StateT s m)
instance (MonadPerhaps m, Monoid w) => MonadPerhaps (Lazy.WriterT w m)
instance (MonadPerhaps m, Monoid w) => MonadPerhaps (Strict.WriterT w m)
instance (MonadPerhaps m, Monoid w) => MonadPerhaps (Lazy.RWST r w s m)
instance (MonadPerhaps m, Monoid w) => MonadPerhaps (Strict.RWST r w s m)
instance MonadPerhaps m => MonadPerhaps (ReaderT r m)
instance MonadPerhaps m => MonadPerhaps (IdentityT m)
