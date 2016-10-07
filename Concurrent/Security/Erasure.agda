open import Lattice
open import Scheduler using (Scheduler)

module Concurrent.Security.Erasure (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Concurrent.Security.Erasure.Base 𝓛 𝓢 public
open import Concurrent.Security.Erasure.LowEq 𝓛 𝓢 public
