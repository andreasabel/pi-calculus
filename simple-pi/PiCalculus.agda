-- A simple evaluator for a π-like calculus
-- using sender and receiver queues.
-- Well-scopedness is ensured by indexed types.
-- Andreas Abel, Cascais, Lisbon, 19 January 2019

{-# OPTIONS --postfix-projections #-}

module PiCalculus where

open import Size
open import Function using (id)

open import Data.Maybe using (Maybe; nothing; just)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Any using (here; there)
open import Data.List.All using (All; []; _∷_; tabulate) renaming (map to mapAll; lookup to lookupAll)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Sublist.Propositional using (_⊆_) renaming (lookup to wkName)
open _⊆_ renaming (base to []; keep to lift; skip to weak)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl)

open import Relation.Binary.PropositionalEquality using (refl)

-- Auxiliary definitions for List.All:

-- Updating at a position.

updateAt : ∀{a p}{A : Set a}{P : A → Set p} {x xs} → x ∈ xs → (P x → P x) → All P xs → All P xs
updateAt () f []
updateAt (here refl) f (px ∷ pxs) = f px ∷ pxs
updateAt (there i)   f (px ∷ pxs) =   px ∷ updateAt i f pxs

-- Insert default element for new names:

wkAllWithDefault :
  ∀ {a p} {A : Set a} {P : A → Set p} (def : ∀{t} → P t) →
  ∀ {Γ Δ} (ρ : Γ ⊆ Δ) → All P Γ → All P Δ
wkAllWithDefault def []       as       = as
wkAllWithDefault def (weak ρ) as       = def ∷ wkAllWithDefault def ρ as
wkAllWithDefault def (lift ρ) (a ∷ as) = a ∷ wkAllWithDefault def ρ as

wkAllList : ∀{a p} {A : Set a} {P : A → Set p} {Γ Δ} (ρ : Γ ⊆ Δ)
  → All (λ t → List (P t)) Γ
  → All (λ t → List (P t)) Δ
wkAllList ρ as = wkAllWithDefault [] ρ as

-- A simple pi-calculus

-- Uni-typed channels

record Ty : Set where

-- A context is the list of the channels in scope.

Cxt = List Ty

-- Expressions of the π-calculus.

data Proc (Γ : Cxt) : Set where

  -- Allocate a new channel.
  new : ∀{t} → Proc (t ∷ Γ) → Proc Γ

  -- Spawn parallel execution.
  par : (p q : Proc Γ) → Proc Γ

  -- Terminate.
  stop : Proc Γ

  -- Send y on x and continue with p.
  send : ∀{t t'} (x : t ∈ Γ) (y : t' ∈ Γ) (p : Proc Γ) → Proc Γ

  -- Receive on x and continue with p.
  recv : ∀{t} (x : t ∈ Γ) t' (p : Proc (t' ∷ Γ)) → Proc Γ


-- Lifting a process to an extended name set (weakening).

wkProc : ∀{Γ Δ} (ρ : Γ ⊆ Δ) (p : Proc Γ) → Proc Δ
wkProc ρ (new p)      = new (wkProc (lift ρ) p)
wkProc ρ (par p q)    = par (wkProc ρ p) (wkProc ρ q)
wkProc ρ stop         = stop
wkProc ρ (send x y p) = send (wkName ρ x) (wkName ρ y) (wkProc ρ p)
wkProc ρ (recv x t p) = recv (wkName ρ x) t (wkProc (lift ρ) p)

-- Extending the channel list by one new channel.

weak1 : ∀{t : Ty} {Γ} → Γ ⊆ (t ∷ Γ)
weak1 = weak (⊆-refl)

-- Substitutions of names for names.

Subst : (Δ Γ : Cxt) → Set
Subst Δ Γ = All (λ t → t ∈ Δ) Γ

-- Identity substitution.

idS : ∀{Γ} → Subst Γ Γ
idS = tabulate id

-- Lifting a substitution under a binder.

liftS : ∀{Δ Γ t} (σ : Subst Δ Γ) → Subst (t ∷ Δ) (t ∷ Γ)
liftS σ = here refl ∷ mapAll there σ

-- Singleton substitution.

sgS : ∀{t Γ} (x : t ∈ Γ) → Subst Γ (t ∷ Γ)
sgS x = x ∷ idS

-- Carrying out a substitution in a process.

substProc : ∀{Δ Γ} (σ : Subst Δ Γ) (p : Proc Γ) → Proc Δ
substProc σ (new p)      = new (substProc (liftS σ) p)
substProc σ (par p q)    = par (substProc σ p) (substProc σ q)
substProc σ stop         = stop
substProc σ (send x y p) = send (lookupAll σ x) (lookupAll σ y) (substProc σ p)
substProc σ (recv x t p) = recv (lookupAll σ x) t (substProc (liftS σ) p)


-- To execute a process, we maintain for each channel a list of senders and receivers
-- that want to communicate on this channel.

-- A process that wants to send something on a channel of type t.

record Sender (Γ : Cxt) (t : Ty) : Set where
  constructor sender
  field
    ty   : Ty
    name : ty ∈ Γ  -- name (=data) to send
    cont : Proc Γ

Senders : (Γ : Cxt) (t : Ty) → Set
Senders Γ t = List (Sender Γ t)

SenderQueue : (Γ : Cxt) → Set
SenderQueue Γ = All (Senders Γ) Γ

-- Weakening

wkSender : ∀{Γ Δ t} (ρ : Γ ⊆ Δ) (s : Sender Γ t) → Sender Δ t
wkSender ρ (sender ty x p) = sender ty (wkName ρ x) (wkProc ρ p)

wkSenders : ∀{Γ Δ t} (ρ : Γ ⊆ Δ) (s : Senders Γ t) → Senders Δ t
wkSenders ρ = map (wkSender ρ)

wkAllSenders : ∀{Γ Δ} (ρ : Γ ⊆ Δ) (ss : SenderQueue Γ) → All (Senders Δ) Δ
wkAllSenders ρ ss = wkAllList ρ (mapAll (wkSenders ρ) ss)

-- A process that want to receive something on a channel of type t.

record Receiver (Γ : Cxt) (t : Ty) : Set where
  constructor receiver
  field
    ty : Ty
    cont : Proc (ty ∷ Γ)

Receivers : (Γ : Cxt) (t : Ty) → Set
Receivers Γ t = List (Receiver Γ t)

ReceiverQueue : (Γ : Cxt) → Set
ReceiverQueue Γ = All (Receivers Γ) Γ

-- Weakening

wkReceiver : ∀{Γ Δ t} (ρ : Γ ⊆ Δ) (s : Receiver Γ t) → Receiver Δ t
wkReceiver ρ (receiver ty p) = receiver ty (wkProc (lift ρ) p)

wkReceivers : ∀{Γ Δ t} (ρ : Γ ⊆ Δ) (s : Receivers Γ t) → Receivers Δ t
wkReceivers ρ = map (wkReceiver ρ)

wkAllReceivers : ∀{Γ Δ} (ρ : Γ ⊆ Δ) (ss : ReceiverQueue Γ) → All (Receivers Δ) Δ
wkAllReceivers ρ ss = wkAllList ρ (mapAll (wkReceivers ρ) ss)

-- Pairing up a sender and a receiver

record MatchingPair Γ Δ : Set where
  constructor matchingPair
  field
    {t}       : Ty
    mpSender    : Sender Γ t
    mpReceiver  : Receiver Γ t
    mpSenders   : All (Senders Γ) Δ
    mpReceivers : All (Receivers Γ) Δ

-- Find pair of a sender and a receiver that could communicate,
-- and remove them from the sender and receiver queues.

findPair : ∀{Γ Δ} → All (Senders Γ) Δ → All (Receivers Γ) Δ → Maybe (MatchingPair Γ Δ)
findPair [] [] = nothing
findPair ((s ∷ ss) ∷ sss) ((r ∷ rs) ∷ rss) = just (matchingPair s r (ss ∷ sss) (rs ∷ rss))
findPair (ss ∷ sss) (rs ∷ rss) with findPair sss rss
... | nothing = nothing
... | just (matchingPair r s sss' rss') = just (matchingPair r s (ss ∷ sss') (rs ∷ rss'))


-- Trace of events

mutual
  record Trace (i : Size) (Γ : Cxt) : Set where
    coinductive
    field force : {j : Size< i} → Trace' j Γ

  data Trace' (i : Size) (Γ : Cxt) : Set where

    -- A new channel has been allocated.
    alloc     : {t : Ty} (tr : Trace i (t ∷ Γ)) → Trace' i Γ

    -- A new process has been spawned.
    spawn     : (tr : Trace i Γ) → Trace' i Γ

    -- Name y was sent on some channel.
    transmit  : ∀{t} (x : t ∈ Γ) (tr : Trace i Γ) → Trace' i Γ

    -- -- Name y was sent on channel x.
    -- transmit  : ∀{t t'} (x : t ∈ Γ) (y : t' ∈ Γ) (tr : Trace i Γ) → Trace' i Γ

    -- A process becomes passive as either sender or receiver.
    enqueue : (tr : Trace i Γ) → Trace' i Γ

    -- All actions have been performed.
    done : Trace' i Γ

    -- No further action is possible.
    deadlock : Trace' i Γ

open Trace

-- State of the evaluator.
--
-- Keep queue of ready processes.
-- Keep queue of processes that want to send on x, for each x.
-- Keep queue of processes that want to receive on x, for each x.

record State (Γ : Cxt) : Set where
  constructor state
  field
    active    : List (Proc Γ)
    senders   : SenderQueue Γ
    receivers : ReceiverQueue Γ

-- Weakening the state

wkState : ∀{Γ Δ} (ρ : Γ ⊆ Δ) → State Γ → State Δ
wkState ρ (state ps ss rs) = state (map (wkProc ρ) ps) (wkAllSenders ρ ss) (wkAllReceivers ρ rs)

-- Running from a state to produce a trace of events.

mutual
  run : ∀{i Γ} → State Γ → Trace i Γ

  -- If no process is active, try to connect a sender to a receiver.
  run (state [] ss rs) = tryTransmit ss rs

  -- Terminated processes are discarded.
  run (state (stop       ∷ ps) ss rs) = run (state ps ss rs)

  -- Flatten a parallel process pair.
  run (state (par p q    ∷ ps) ss rs) .force = spawn (run (state (p ∷ q ∷ ps) ss rs))

  -- Allocate a new channel; need to weaken the state.
  run (state (new t      ∷ ps) ss rs) .force = alloc (run (wkState weak1 (state ps ss rs)))

  -- Enqueue a sender.
  run (state (send x y p ∷ ps) ss rs) .force = enqueue (run (state ps (updateAt x (sender _ y p ∷_) ss) rs))

  -- Enqueue a receiver.
  run (state (recv x t p ∷ ps) ss rs) .force = enqueue (run (state ps ss (updateAt x (receiver t p ∷_) rs)))

  -- Look for a pair of sender and receiver on the same channel.
  -- If successful, let them communicate and enqueue them in the active processes.
  -- If unsuccessful, we are deadlocked.

  tryTransmit : ∀{i Γ} → SenderQueue Γ → ReceiverQueue Γ → Trace i Γ
  tryTransmit [] [] .force = done
  tryTransmit ss rs .force with findPair ss rs
  ... | nothing = deadlock
  ... | just (matchingPair (sender _ y p) (receiver _ q) ss' rs') =

    -- Transmit value y to receiver q.
    let q' = substProc (sgS y) q

    -- Both sender and receiver are now active again.
    in  transmit y (run (state (p ∷ q' ∷ []) ss' rs'))

-- Evaluation of a closed process to a trace.

eval : ∀{i} → Proc [] → Trace i []
eval p = run (state (p ∷ []) [] [])
