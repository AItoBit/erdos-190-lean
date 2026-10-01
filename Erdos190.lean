module

public import Mathlib

/-!
# Erdős Problem 190

*Reference:* [erdosproblems.com/190](https://www.erdosproblems.com/190)

Let `H k` be the smallest `N` such that every finite colouring of `{1, …, N}` (into any number
of colours) contains a `k`-term arithmetic progression which is either monochromatic or rainbow
(all elements of different colours). Is it true that `H(k)^(1/k) / k → ∞`?

**Status.** Solved, answer *yes* (Bae 2026: `H(k) ≥ k^((2-o(1))k)`; Fox–Hunter 2026
independently: `H(k) ≥ k^((1-o(1)) k log k)`).

**What is proved here.** A self-contained proof of the qualitative answer:

* `canonicalAP_lower_bound` (unconditional): for every `C`, for all large `k`, every `N` such
  that all colourings of `{1, …, N}` have a monochromatic or rainbow `k`-AP satisfies
  `N > (C k)^k`.
* `erdos_190`: hence `H(k)^(1/k) / k → ∞`, under the hypothesis that `H k` is well defined
  (existence of such an `N`, due to Erdős–Graham via Szemerédi's theorem, which is not in
  Mathlib and is taken as a hypothesis).

**Proof outline.** A colouring with `k - 1` colours has no rainbow `k`-AP, so it suffices to
bound the van der Waerden number `W(k - 1, k)` from below:
1. union bound: `W(r, k) > N` whenever `N ^ 2 < r ^ (k - 1)` (`noMonoAP_of_sq_lt`);
2. a Blankenship–Cummings–Taranchuk type product step: for a prime `p ≤ k` and
   `r ≤ p (r - r')`, `W(r, k) - 1 ≥ p (W(r', k) - 1)` (`NoMonoAP.step`);
3. with a Bertrand prime `k/2 < p ≤ k - 1`, apply step 2 with `r - r' = 1` from `k/8` up to `p`
   colours and then with `r - r' = 2` up to `k - 1` colours, giving
   `W(k - 1, k) ≥ (k/8)^((9/8 - o(1)) k)`, which beats `(C k)^k`.
-/

@[expose] public section

open Filter

namespace Erdos190

/-- `CanonicalAP k N`: every colouring of `{1, …, N}` (colours in `ℕ`; any finite colouring can
be relabelled this way) contains a `k`-term arithmetic progression `a, a + d, …, a + (k-1)d`
with `d > 0`, inside `{1, …, N}`, which is monochromatic or rainbow. -/
def CanonicalAP (k N : ℕ) : Prop :=
  ∀ c : ℕ → ℕ, ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
    ((∀ i < k, c (a + i * d) = c a) ∨ Set.InjOn (fun i ↦ c (a + i * d)) (Set.Iio k))

/-- `H k` is the least `N` with `CanonicalAP k N` (by convention `0` if no such `N` exists). -/
noncomputable def H (k : ℕ) : ℕ := sInf {N | CanonicalAP k N}

/-- `NoMonoAP r k N`: there is an `r`-colouring of `{0, …, N - 1}` with no monochromatic
`k`-term arithmetic progression, i.e. the van der Waerden number satisfies `W(r, k) > N`. -/
def NoMonoAP (r k N : ℕ) : Prop :=
  ∃ χ : ℕ → ℕ, (∀ x, χ x < r) ∧
    ∀ a d, 0 < d → a + (k - 1) * d < N → ∃ i < k, χ (a + i * d) ≠ χ a

/-- Monotonicity in the number of colours and in the length of the interval. -/
lemma NoMonoAP.mono {r r' k N N' : ℕ} (h : NoMonoAP r k N) (hr : r ≤ r') (hN : N' ≤ N) :
    NoMonoAP r' k N' := by
  obtain ⟨χ, hχ, h⟩ := h
  exact ⟨χ, fun x ↦ (hχ x).trans_le hr, fun a d hd had ↦ h a d hd (had.trans_le hN)⟩

/-- A colouring with `k - 1` colours has no rainbow `k`-term progression, so a `(k-1)`-colouring
without monochromatic `k`-APs witnesses `¬ CanonicalAP k N`. -/
lemma not_canonicalAP_of_noMonoAP {k N : ℕ} (hk : 1 ≤ k) (h : NoMonoAP (k - 1) k N) :
    ¬ CanonicalAP k N := by
  obtain ⟨χ, hχ, hgood⟩ := h
  intro hc
  obtain ⟨a, d, hd, ha, haN, hmono | hrain⟩ := hc (fun x ↦ χ (x - 1))
  · obtain ⟨i, hi, hne⟩ := hgood (a - 1) d hd (by omega)
    apply hne
    have h : χ (a + i * d - 1) = χ (a - 1) := hmono i hi
    rwa [show a + i * d - 1 = a - 1 + i * d by omega] at h
  · have := Finset.card_le_card_of_injOn (s := Finset.range k) (t := Finset.range (k - 1))
      (fun i ↦ χ (a + i * d - 1)) (fun _ _ ↦ Finset.mem_range.2 (hχ _))
      (fun x hx y hy hxy ↦ hrain (Finset.mem_range.1 hx) (Finset.mem_range.1 hy) hxy)
    simp at this
    omega

/-- Colourings constant on `A` are determined by one colour and their values off `A`. -/
lemma card_filter_constOn_le {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) (A : Finset α)
    (x₀ : α) : (Finset.univ.filter fun f : α → Fin r ↦ ∀ x ∈ A, f x = f x₀).card ≤
      r * r ^ (Fintype.card α - A.card) := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun f : α → Fin r ↦ ∀ x ∈ A, f x = f x₀) (t := Finset.univ)
    (fun f : α → Fin r ↦ (f x₀, fun y : {x // x ∉ A} ↦ f y)) (fun _ _ ↦ Finset.mem_univ _)
    (by
      intro f hf g hg hfg
      have hf' : ∀ x ∈ A, f x = f x₀ := by simpa using hf
      have hg' : ∀ x ∈ A, g x = g x₀ := by simpa using hg
      simp only [Prod.mk.injEq, funext_iff, Subtype.forall] at hfg
      funext x
      by_cases hx : x ∈ A
      · rw [hf' x hx, hg' x hx, hfg.1]
      · exact hfg.2 x hx)
  simpa [Fintype.card_subtype_compl, Finset.card_univ] using h

/-- Union bound: if `N ^ 2 < r ^ (k - 1)` then a random `r`-colouring works. -/
lemma noMonoAP_of_sq_lt {r k N : ℕ} (hr : 0 < r) (hk : 2 ≤ k) (h : N ^ 2 < r ^ (k - 1)) :
    NoMonoAP r k N := by
  rcases lt_or_ge N k with hNk | hkN
  · refine ⟨fun _ ↦ 0, fun _ ↦ hr, fun a d hd had ↦ ?_⟩
    have : k - 1 ≤ (k - 1) * d := Nat.le_mul_of_pos_right _ hd
    omega
  have hN : 0 < N := by omega
  let T : Finset (ℕ × ℕ) := (Finset.range N ×ˢ Finset.range N).filter
    fun ad ↦ 0 < ad.2 ∧ ad.1 + (k - 1) * ad.2 < N
  let pt : ℕ × ℕ → ℕ → Fin N := fun ad i ↦ ⟨(ad.1 + i * ad.2) % N, Nat.mod_lt _ hN⟩
  let A : ℕ × ℕ → Finset (Fin N) := fun ad ↦ (Finset.range k).image (pt ad)
  let Bad : ℕ × ℕ → Finset (Fin N → Fin r) := fun ad ↦
    Finset.univ.filter fun f ↦ ∀ x ∈ A ad, f x = f (pt ad 0)
  have hpt : ∀ ad ∈ T, ∀ i < k, ((pt ad i : Fin N) : ℕ) = ad.1 + i * ad.2 := by
    intro ad had i hi
    simp only [T, Finset.mem_filter] at had
    have : i * ad.2 ≤ (k - 1) * ad.2 := Nat.mul_le_mul_right _ (by omega)
    exact Nat.mod_eq_of_lt (by omega)
  have hA : ∀ ad ∈ T, (A ad).card = k := by
    intro ad had
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hd : 0 < ad.2 := by simp only [T, Finset.mem_filter] at had; exact had.2.1
    have := congrArg Fin.val hij
    rw [hpt ad had i (by simpa using hi), hpt ad had j (by simpa using hj)] at this
    exact Nat.eq_of_mul_eq_mul_right hd (by omega)
  have hBad : ∀ ad ∈ T, (Bad ad).card ≤ r * r ^ (N - k) := by
    intro ad had
    have := card_filter_constOn_le r (A ad) (pt ad 0)
    rw [Fintype.card_fin, hA ad had] at this
    convert this using 2
    simp only [Bad]
    congr
  have hT : T.card ≤ N ^ 2 := by
    calc T.card ≤ (Finset.range N ×ˢ Finset.range N).card := Finset.card_filter_le _ _
      _ = N ^ 2 := by simp [sq]
  have hcard : (T.biUnion Bad).card < (Finset.univ : Finset (Fin N → Fin r)).card := by
    calc (T.biUnion Bad).card ≤ ∑ ad ∈ T, (Bad ad).card := Finset.card_biUnion_le
      _ ≤ ∑ _ad ∈ T, r * r ^ (N - k) := Finset.sum_le_sum hBad
      _ = T.card * (r * r ^ (N - k)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ N ^ 2 * (r * r ^ (N - k)) := Nat.mul_le_mul_right _ hT
      _ < r ^ (k - 1) * (r * r ^ (N - k)) := Nat.mul_lt_mul_of_pos_right h (by positivity)
      _ = r ^ N := by rw [← pow_succ', ← pow_add]; congr 1; omega
      _ = _ := by simp
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨fun x ↦ if hx : x < N then (f ⟨x, hx⟩ : ℕ) else 0, fun x ↦ ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact (f _).isLt
    · exact hr
  intro a d hd had
  have hadT : (a, d) ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    have : d ≤ (k - 1) * d := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have : f ∉ Bad (a, d) := fun hmem ↦ hf (Finset.mem_biUnion.2 ⟨_, hadT, hmem⟩)
  simp only [Bad, A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_image,
    Finset.mem_range, not_forall] at this
  obtain ⟨i, hi, hne⟩ := this
  refine ⟨i, hi, ?_⟩
  have h1 := hpt _ hadT i hi
  have h0 := hpt _ hadT 0 (by omega)
  simp only [zero_mul, add_zero] at h0
  have hlt1 : a + i * d < N := h1 ▸ (pt (a, d) i).isLt
  have hlt0 : a < N := h0 ▸ (pt (a, d) 0).isLt
  simp only [hlt1, hlt0, dite_true]
  intro heq
  apply hne
  have e1 : pt (a, d) i = ⟨a + i * d, hlt1⟩ := Fin.ext h1
  have e0 : pt (a, d) 0 = ⟨a, hlt0⟩ := Fin.ext h0
  rw [e1, e0]
  exact Fin.ext heq

/-- For a prime `p ∤ d`, the progression `a + i d`, `i < p`, meets every residue class. -/
lemma exists_lt_add_mul_mod_eq {p : ℕ} (hp : p.Prime) {d : ℕ} (hd : ¬ p ∣ d) (a s : ℕ)
    (hs : s < p) : ∃ i < p, (a + i * d) % p = s := by
  have := Fact.mk hp
  have hd0 : (d : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  refine ⟨(((s : ZMod p) - a) * (d : ZMod p)⁻¹).val, ZMod.val_lt _, ?_⟩
  have key : (((a + (((s : ZMod p) - a) * (d : ZMod p)⁻¹).val * d : ℕ)) : ZMod p) = s := by
    push_cast
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hd0]
    ring
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hs] at key
  exact key

/-- Blankenship–Cummings–Taranchuk type step: for a prime `p ≤ k`, a good `r'`-colouring of
`{0, …, n-1}` yields a good `r`-colouring of `{0, …, pn-1}` provided `r ≤ p (r - r')`. -/
lemma NoMonoAP.step {r r' k n p : ℕ} (hp : p.Prime) (hpk : p ≤ k) (hr' : r' < r)
    (hrp : r ≤ p * (r - r')) (h : NoMonoAP r' k n) : NoMonoAP r k (p * n) := by
  obtain ⟨χ, hχ, hgood⟩ := h
  set s := r - r' with hs_def
  have hs : 0 < s := by omega
  refine ⟨fun x ↦ (χ (x / p) + s * (x % p + 1)) % r, fun x ↦ Nat.mod_lt _ (by omega), ?_⟩
  intro a d hd had
  by_contra hall
  push Not at hall
  by_cases hpd : p ∣ d
  · obtain ⟨e, rfl⟩ := hpd
    have he : 0 < e := Nat.pos_of_mul_pos_left hd
    have hdiv : ∀ i, (a + i * (p * e)) / p = a / p + i * e := fun i ↦ by
      rw [show a + i * (p * e) = a + p * (i * e) by ring, Nat.add_mul_div_left _ _ hp.pos]
    have hmod : ∀ i, (a + i * (p * e)) % p = a % p := fun i ↦ by
      rw [show a + i * (p * e) = a + p * (i * e) by ring, Nat.add_mul_mod_self_left]
    obtain ⟨i, hi, hne⟩ := hgood (a / p) e he (by
      have h1 : p * (a / p) ≤ a := Nat.mul_div_le a p
      have h2 : p * (a / p + (k - 1) * e) < p * n := by nlinarith
      exact lt_of_mul_lt_mul_left h2 (Nat.zero_le _))
    apply hne
    have := hall i hi
    simp only [hdiv, hmod] at this
    have h3 := Nat.ModEq.add_right_cancel' _ this
    have := hχ (a / p + i * e)
    have := hχ (a / p)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
  · set c := (χ (a / p) + s * (a % p + 1)) % r with hc
    have hcr : c < r := Nat.mod_lt _ (by omega)
    have hcs : c / s < p := by
      rw [Nat.div_lt_iff_lt_mul hs]; nlinarith
    obtain ⟨i, hi, hres⟩ := exists_lt_add_mul_mod_eq hp hpd a (c / s) hcs
    have := hall i (by omega)
    simp only [hres] at this
    have hχv := hχ ((a + i * d) / p)
    have h1 : s * (c / s + 1) ≤ c + s := by
      rw [mul_add, mul_one]; have := Nat.mul_div_le c s; omega
    have h2 : c < s * (c / s + 1) := by
      rw [mul_add, mul_one]; have := Nat.lt_mul_div_succ c hs; linarith
    have h4 := Nat.div_add_mod (χ ((a + i * d) / p) + s * (c / s + 1)) r
    rw [this] at h4
    obtain h5 | h5 := Nat.eq_zero_or_pos ((χ ((a + i * d) / p) + s * (c / s + 1)) / r)
    · rw [h5] at h4; omega
    · have := Nat.mul_le_mul_left r h5
      omega

/-- Iterating `NoMonoAP.step` `j` times, adding `s` colours each time. -/
lemma NoMonoAP.iterate {r₀ k n p s : ℕ} (hp : p.Prime) (hpk : p ≤ k) (hs : 0 < s)
    (h : NoMonoAP r₀ k n) : ∀ j, r₀ + s * j ≤ s * p → NoMonoAP (r₀ + s * j) k (p ^ j * n) := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ j ih =>
    intro hj
    have := (ih (by nlinarith)).step (r := r₀ + s * (j + 1)) hp hpk (by nlinarith)
      (by rw [show r₀ + s * (j + 1) - (r₀ + s * j) = s by rw [mul_add]; omega]; linarith)
    rwa [pow_succ, mul_comm _ p, mul_assoc]

/-- The quantitative heart: `W(k - 1, k) > (C k) ^ k` for all large `k`. -/
lemma eventually_noMonoAP (C : ℕ) : ∀ᶠ k in atTop, NoMonoAP (k - 1) k ((C * k) ^ k) := by
  filter_upwards [eventually_ge_atTop (8 * (16 * C + 16) ^ 32 + 64)] with k hk
  set D := 16 * C + 16 with hD_def
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
  set r₀ := k / 8 with hr₀_def
  set m := (k - 2) / 2 with hm_def
  set j := (k - 1 - p) / 2 with hj_def
  have hr₀D : D ^ 32 ≤ r₀ := by omega
  have hr₀2 : 2 ≤ r₀ := by omega
  have hr₀p : r₀ ≤ p := by omega
  have hpk : p ≤ k := by omega
  have hpk1 : p ≤ k - 1 := by
    by_contra hcon
    have h2 : p = 2 * (k / 2) := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 ⟨k / 2, h2⟩)
    omega
  have base : NoMonoAP r₀ k (r₀ ^ m) := noMonoAP_of_sq_lt (by omega) (by omega)
    (by rw [← pow_mul]; exact Nat.pow_lt_pow_right (by omega) (by omega))
  have s1 := base.iterate hp hpk one_pos (p - r₀) (by omega)
  rw [show r₀ + 1 * (p - r₀) = p by omega] at s1
  have s2 := s1.iterate hp hpk two_pos j (by omega)
  refine s2.mono ?_ ?_
  · omega
  have hCk : C * k ≤ D * r₀ := by
    have : k < 8 * (r₀ + 1) := by omega
    nlinarith
  calc (C * k) ^ k ≤ (D * r₀) ^ k := Nat.pow_le_pow_left hCk k
    _ = D ^ k * r₀ ^ k := mul_pow _ _ _
    _ ≤ r₀ ^ (k / 16) * r₀ ^ k := by
      refine Nat.mul_le_mul_right _ ?_
      calc D ^ k ≤ D ^ (32 * (k / 16)) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = (D ^ 32) ^ (k / 16) := pow_mul _ _ _
        _ ≤ r₀ ^ (k / 16) := Nat.pow_le_pow_left hr₀D _
    _ = r₀ ^ (k + k / 16) := by rw [← pow_add, add_comm]
    _ ≤ r₀ ^ (j + (p - r₀) + m) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = r₀ ^ j * (r₀ ^ (p - r₀) * r₀ ^ m) := by rw [pow_add, pow_add, mul_assoc]
    _ ≤ p ^ j * (p ^ (p - r₀) * r₀ ^ m) := by gcongr

/-- Unconditional form of the answer: for every `C`, for all large `k`, every `N` with the
canonical property satisfies `N > (C k) ^ k`. -/
theorem canonicalAP_lower_bound (C : ℕ) :
    ∀ᶠ k in atTop, ∀ N, CanonicalAP k N → (C * k) ^ k < N := by
  filter_upwards [eventually_noMonoAP C, eventually_ge_atTop 1] with k hk hk1 N hN
  by_contra hlt
  exact not_canonicalAP_of_noMonoAP hk1 (hk.mono le_rfl (not_lt.1 hlt)) hN

/-- **Erdős Problem 190** (answer: yes), assuming `H k` is well defined, i.e. that the canonical
van der Waerden property holds for some `N` (Erdős–Graham, via Szemerédi's theorem). -/
theorem erdos_190 (hH : ∀ k, ∃ N, CanonicalAP k N) :
    Tendsto (fun k : ℕ ↦ (H k : ℝ) ^ (1 / k : ℝ) / k) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [canonicalAP_lower_bound ⌈b⌉₊, eventually_ge_atTop 1] with k hk hk1
  have hmem : CanonicalAP k (H k) := Nat.sInf_mem (hH k)
  have hlt : (((⌈b⌉₊ * k) ^ k : ℕ) : ℝ) < H k := by exact_mod_cast hk _ hmem
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have h1 : ((⌈b⌉₊ : ℝ) * k) ≤ (H k : ℝ) ^ (1 / k : ℝ) := by
    have := Real.rpow_le_rpow (z := (1 / k : ℝ)) (by positivity) hlt.le (by positivity)
    rw [Nat.cast_pow, Nat.cast_mul, one_div, Real.pow_rpow_inv_natCast (by positivity)
      (by omega)] at this
    rwa [one_div]
  rw [le_div_iff₀ hkpos]
  calc b * k ≤ ⌈b⌉₊ * k := by gcongr; exact Nat.le_ceil b
    _ ≤ _ := h1

end Erdos190
