/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/

import GB.FinsuppAlg.Order
import GB.AddSubtrCommMonoid
import GB.Sbt

variable {𝕜 : Type} {M : Type}
variable [DecidableEq 𝕜] [Field 𝕜] [LinearOrderedAddSubtrCommMonoid N]
variable [DecidableRel (· ━? · : N → N → Prop)]

open Finsupp Finset FinsuppAlg LinearOrderedAddSubtrCommMonoid

instance : Inhabited N where
  default := Zero.zero

instance : Monad <| WithBot := inferInstanceAs <| Monad <| Option

def lm! (f : alg 𝕜 N) : N := lm f|>.recBotCoe default id

def reducible (f : alg 𝕜 N) (n : N) : Bool := if h : f = 0 then true else decide <| n ━? (lm' f h)

def sPoly (f g : alg 𝕜 N) : alg 𝕜 N :=
  match lm f, lm g with
  | none, _ => -g
  | _, none => f
  | WithBot.some m₁, WithBot.some m₂ =>
      single' (lcs m₁ m₂ - m₁) (1 / lc f) * f - single' (lcs m₁ m₂ - m₂) (1 / lc g) * g

variable (G : Array <| alg 𝕜 N)

def lms : Array N := G.mapM lm|>.recBotCoe #[] id

def reduceSel (n : N) : Option <| alg 𝕜 N :=
  let arr := G.filter (fun g => reducible g n)|>.qsort (fun g₁ g₂ => lm g₁ ≥ lm g₂)
  arr[0]?

def reduce (f : alg 𝕜 N) (h : alg 𝕜 N) : alg 𝕜 N :=
  if h' : f = 0 then 0 else if h'' : h = 0 then f else
    f - single' ((lm' f h') - (lm' h h'')) (lc f / lc h) * h

/- Make TR -/
partial def leadReduce (G : Array <| alg 𝕜 N) (f : alg 𝕜 N) : alg 𝕜 N :=
  if h' : f = 0 then 0
  else reduceSel G (lm' f h')|>.elim f <| fun h => leadReduce G <| reduce f h

/- Make TR -/
partial def fullReduce (G : Array <| alg 𝕜 N) (f : alg 𝕜 N) : alg 𝕜 N :=
  if h' : f = 0 then 0
  else reduceSel G (lm' f h')|>.elim ((lt f) + (fullReduce G (tail f)))
    (fun h => fullReduce G <| reduce f h)

def tailReduce (G : Array <| alg 𝕜 N) (f : alg 𝕜 N) := lt f - (fullReduce G <| tail f)

def sortPair (C : Array <| alg 𝕜 N × alg 𝕜 N) : Array <| alg 𝕜 N × alg 𝕜 N :=
  C.qsort (fun p q => lm p.2 ≥ lm q.2)

partial def loopC (C D : Array <| alg 𝕜 N × alg 𝕜 N) : Array <| alg 𝕜 N × alg 𝕜 N :=
  if C.isEmpty then D else
    let sorted := sortPair C
    sorted[0]?.elim D fun q =>
      let C' := Array.mk <| List.drop 1 sorted.data
      let u := lcs (lm! q.1) (lm! q.2)
        if u = (lm! q.1) + (lm! q.2) then
          loopC C' <| D.push q
        else
          let new := C'.append D|>.all (fun q => !u ━? (lcs (lm! q.1) (lm! q.2)))
          if new then loopC C' <| D.push q
          else loopC C' D
-- termination_by loopC C => C.size

def PNewAux (D : Array <| alg 𝕜 N × alg 𝕜 N) : Array <| alg 𝕜 N × alg 𝕜 N :=
  D.filter (fun q => lcs (lm! q.1) (lm! q.2) != (lm! q.1) + (lm! q.2))

def PNew (Pnew : Array <| alg 𝕜 N × alg 𝕜 N) (p : alg 𝕜 N × alg 𝕜 N) (f : alg 𝕜 N) :
    Array <| alg 𝕜 N × alg 𝕜 N :=
  let mf := lm! f
  let m1 := lm! p.1
  let m2 := lm! p.2
  let lcm' := lcs m1 m2
  if lcm' ━? mf || lcs m1 mf = lcm' || lcs m2 mf = lcm' then
    Pnew.push p
  else Pnew

def gmUpdateP (G : Array <| alg 𝕜 N) (P : Array <| alg 𝕜 N × alg 𝕜 N) (f : alg 𝕜 N) :
    Array <| alg 𝕜 N × alg 𝕜 N :=
  let C : Array <| alg 𝕜 N × alg 𝕜 N := G.map (fun g => ⟨f,g⟩)
  let Pnew := loopC C #[]|>.filter (fun q => lcs (lm! q.1) (lm! q.2) != (lm! q.1) + (lm! q.2))
  P.foldl (fun arr p => PNew arr p f) Pnew

def gmUpdateG (G : Array <| alg 𝕜 N) (f : alg 𝕜 N) : Array <| alg 𝕜 N :=
  G.filter (fun g => !(lm! g) ━? (lm! f))|>.push f

def generate (G F : Array <| alg 𝕜 N) (P : Array <| alg 𝕜 N × alg 𝕜 N) :
    (Array <| alg 𝕜 N) × (Array <| alg 𝕜 N × alg 𝕜 N) :=
  F.foldl (fun H f => ⟨gmUpdateG H.1 <| fullReduce H.1 f, gmUpdateP H.1 H.2 <| fullReduce H.1 f⟩) ⟨G,P⟩

partial def processCP (G : Array <| alg 𝕜 N) (P : Array <| alg 𝕜 N × alg 𝕜 N) :
    (Array <| alg 𝕜 N) × (Array <| alg 𝕜 N × alg 𝕜 N) :=
    (sortPair P)[0]?|>.elim ⟨G,P⟩ fun p =>
      let P' := Array.mk <| (sortPair P).data.drop 1
      let h := fullReduce G <| sPoly p.1 p.2
      if h ≠ 0 then
        let G' := gmUpdateG G h|>.map (fun g => tailReduce G g)
        let P' := gmUpdateP G P' h
        processCP G' P'
      else
        processCP G P'

def buchberger (F : Array <| alg 𝕜 N) : Array <| alg 𝕜 N :=
  let H := generate #[] F #[]
  processCP H.1 H.2|>.1

