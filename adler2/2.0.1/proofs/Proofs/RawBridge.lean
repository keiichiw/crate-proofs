module
public import Proofs.Loop4

@[expose] public section
open Aeneas.Std
namespace adler2

theorem normalize_rawStep (s : Nat × Nat) (byte : U8) :
    normalize (rawStep s byte) = step (normalize s) byte := by
  simp [normalize, rawStep, step, Nat.add_mod]

theorem normalize_rawRun (s : Nat × Nat) (bytes : List U8) :
    normalize (rawRun s bytes) = run s bytes := by
  induction bytes generalizing s with
  | nil => simp [rawRun, run]
  | cons byte rest ih =>
      change normalize (rawRun (rawStep s byte) rest) = run s (byte :: rest)
      rw [ih]
      simp only [run, List.foldl_cons]
      rw [normalize_rawStep]

theorem run_of_mod (a b ra rb : Nat) (bytes : List U8)
    (ha : a % modulus = ra) (hb : b % modulus = rb)
    (hra : ra < modulus) (hrb : rb < modulus) :
    run (a, b) bytes = run (ra, rb) bytes := by
  simp [run, normalize, ha, hb,
    Nat.mod_eq_of_lt hra, Nat.mod_eq_of_lt hrb]

end adler2
