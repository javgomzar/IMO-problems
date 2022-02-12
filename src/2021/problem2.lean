import data.real.basic
import data.real.sqrt
import data.set.basic
import algebra.big_operators.basic
import tactic

open real
open finset
open_locale big_operators

noncomputable theory

notation `|`x`|` := abs x

/-
 # Definitions 
-/

def f_add : ℝ → ℝ → ℝ := λ x y, sqrt (|x + y|)

def f_add_move {r : ℝ} : ℝ → ℝ → ℝ := λ x y, f_add (x + r) (y + r)

def f_sub : ℝ → ℝ → ℝ := λ x y, sqrt (|x - y|)

def f_move {s : finset ℝ} : ℝ → ℝ := λ r, ∑ x y in s, f_add (x + r) (y + r)

def f_aux (x y : ℝ) : ℝ → ℝ := λ r, f_add (x + r) (y + r)


/- 
# Lemmas 

Here are some simple lemmas about the definitions we have just given and some auxiliary facts.
-/

lemma f_add_move_comm (r : ℝ) : ∀ x y, f_add (x + r) (y + r) = f_add (y + r) (x + r) := 
begin intros x y, unfold f_add, ring_nf end

lemma f_add_comm : ∀ x y, f_add x y = f_add y x := 
begin 
  have := f_add_move_comm 0,
  simp at this,
  assumption,
end

lemma f_sub_comm : ∀ x y, f_sub x y = f_sub y x := 
begin intros x y, unfold f_sub, rw abs_sub_comm end

@[simp] lemma f_add_zero {x : ℝ} : f_add 0 x = sqrt (|x|) :=
begin unfold f_add, ring_nf end

@[simp] lemma f_sub_diag_zero {x : ℝ} : f_sub x x = 0 := 
begin unfold f_sub, simp end

@[simp] lemma f_sub_zero {x : ℝ} : f_sub 0 x = sqrt (|x|) :=
begin unfold f_sub, ring_nf, rw abs_neg end

@[simp] lemma f_sub_move {x y r : ℝ} : f_sub (x + r) (y + r) = f_sub x y :=
begin unfold f_sub, ring_nf end

lemma sum_f_sub_move {x : ℝ} {s : finset ℝ} (r : ℝ) : ∑ y in s, f_sub (x + r) (y + r) = ∑ y in s, f_sub x y :=
begin unfold f_sub, ring_nf end

lemma add_to_sub {x y : ℝ} : f_add (-x) y = f_sub x y :=
begin
  unfold f_add f_sub,
  rw add_comm,
  ring_nf,
  rw abs_sub_comm,
end

lemma left_lt_or_right_lt_of_add_lt_two_mul {a b c : ℝ} : a + b < 2*c → a < c ∨ b < c :=
begin
  intro h,
  by_contradiction h',
  push_neg at h',
  have := add_le_add h'.1 h'.2,
  linarith,
end 


/- 
# Sum lemmas 

  Here are some lemmas about finite sums. Most of them are necessary because of the double sums.
-/

lemma sum_eq_sum {f g : ℝ → ℝ} {s : finset ℝ}: (∀ x, x ∈ s → f x = g x) → ∑ x in s, f x = ∑ x in s, g x :=
begin
  intro h,
  rw sum_eq_sum_iff_of_le,
  exact h,
  intros i hi,
  apply le_of_eq,
  exact h i hi,
end

lemma sum_add_to_sum_sub {a b r : ℝ} {s : finset ℝ}: a + b = 0 → ∑ x in s, f_add a (x + r) = ∑ x in s, f_sub b (x + r) := begin
  intro h,
  rw sum_eq_sum,
  intros x hx,
  rw add_eq_zero_iff_eq_neg at h,
  rw h,
  exact add_to_sub,
end

/- If a function is commutative, we can change the order of the indexes in a double sum -/
lemma change_index {s₁ s₂ : finset ℝ} {f : ℝ → ℝ → ℝ} : (∀ x y : ℝ, f x y = f y x) → ∑ x in s₁, ∑ y in s₂, f x y = ∑ x in s₂, ∑ y in s₁, f x y :=
begin
  intro h_comm,
  rw ← sum_product',
  rw sum_product_right,
  apply sum_eq_sum,
  intros x hx,
  apply sum_eq_sum,
  intros y hy,
  exact h_comm y x,
end

lemma le_sum_of_single {r : ℝ} {s : finset ℝ} {f : ℝ → ℝ} : (0 ≤ f ∧ ∃ x, x ∈ s ∧ r ≤ f x) → r ≤ ∑ x in s, f x :=
begin
  rintros ⟨f_nonneg, x, h_in, hx⟩,
  apply le_trans hx,
  rw sum_eq_sum_diff_singleton_add h_in,
  simp,
  apply sum_nonneg,
  intros y hy,
  specialize f_nonneg y,
  simp at f_nonneg,
  exact f_nonneg,
end

lemma sum_union' {f : ℝ → ℝ → ℝ} {s : finset ℝ} {r : ℝ} (h_in : r ∈ s) (h_comm : ∀ x y : ℝ, f x y = f y x) : ∑ x y in s, f x y = ∑ x y in s \ {r}, f x y + 2 * ∑ x in s \ {r}, f r x + f r r :=
begin
  have h₁ := sum_eq_sum_diff_singleton_add h_in (f r),
  have h₂ := sum_eq_sum_diff_singleton_add h_in (λ x, ∑ y in s, f x y),
  simp at h₂,
  rw h₁ at h₂,
  rw h₂,
  clear h₂,
  rw← add_assoc,
  simp,
  rw change_index h_comm,
  have h₃ := sum_eq_sum_diff_singleton_add h_in (λ x, ∑ y in s \ {r}, f x y),
  simp at h₃,
  rw h₃,
  ring,
end

lemma sum_union'' {f : ℝ → ℝ → ℝ} {s : finset ℝ} (r₁ r₂ : ℝ) (h_in : r₁ ∈ s ∧ r₂ ∈ s ∧ r₁ ≠ r₂) (h_comm : ∀ x y : ℝ, f x y = f y x) : ∑ x y in s, f x y = ∑ x y in s \ {r₁, r₂}, f x y + 2 * ∑ x in s \ {r₁, r₂}, f r₁ x + 2 * ∑ x in s \ {r₁, r₂}, f r₂ x + f r₁ r₁ + f r₂ r₂ + 2*f r₁ r₂ :=
begin
  have h₁ := @sum_union' f s r₁ (by tidy) h_comm,
  have h₂ := @sum_union' f (s \ {r₁}) r₂ (by tidy) h_comm,
  rw h₁,
  clear h₁,
  rw h₂,
  clear h₂,
  rcases h_in with ⟨h_r₁, h_r₂, h_ne⟩,
  have h : r₂ ∈ s \ {r₁} := by tidy,
  have h₃ := sum_eq_sum_diff_singleton_add h (f r₁),
  rw h₃,
  have : s \ {r₁} \ {r₂} = s \ {r₁, r₂} := by tidy,
  rw this,
  ring,
end

lemma sum_map' (i : ℝ ↪ ℝ) {s : finset ℝ} {f : ℝ → ℝ → ℝ} : ∑ x y in map i s, f x y = ∑ x y in s, f (i x) (i y) :=
begin rw [sum_map, sum_eq_sum], intros x hx, rw sum_map end

lemma sum_add_distrib' {s : finset ℝ} {f g : ℝ → ℝ → ℝ} : ∑ x y in s, f x y + ∑ x y in s, g x y = ∑ x y in s, (f x y + g x y) :=
begin 
  rw ← sum_add_distrib,
  apply sum_eq_sum,
  intros x hx,
  rw ← sum_add_distrib,
end


/-
 # Analysis requirements 
 
  Surprisingly we will need some facts from analysis to solve this problem. We prove that a relevant function has a global minimum and we will also use that the square root is a concave function (separately on each side of the real line) in order to apply jensen's lemma.
-/

/- This is not exactly concavity: It's concavity but only between two points with the same sign -/
def is_concave (f : ℝ → ℝ) : Prop := ∀ x y t : ℝ, t ∈ set.Ioo (0 : ℝ) (1 : ℝ) → 0 < x * y → x ≠ y → f (t * x + (1 - t) * y) > t * f x + (1 - t) * f y

def unbounded (f : ℝ → ℝ) : Prop := ∀ M > 0, ∃ K ≥ 0, ∀ y, K ≤ |y| → M ≤ f y

lemma f_is_unbounded {s : finset ℝ} (hs : s.nonempty) : unbounded (@f_move s) := 
begin 
  intros M hM,
  cases hs with x hx,
  use M^2 + |x|,
  split,
  { exact add_nonneg (sq_nonneg M) (abs_nonneg x) },
  {
    intros r hr,
    unfold f_move,
    apply le_sum_of_single,
    split,
    {
      intro x,
      simp,
      apply sum_nonneg,
      intros y hy,
      apply sqrt_nonneg,
    },
    {
      use x,
      split,
      { exact hx },
      { 
        apply le_sum_of_single,
        split,
        { intro y, apply sqrt_nonneg, },
        {
          use x,
          split,
          { exact hx },
          { 
            unfold f_add, 
            ring_nf, 
            rw [← mul_add, abs_mul, @sqrt_mul (|2|) (by norm_num)],
            simp,
            have : sqrt (|x + r|) ≤ sqrt 2 * sqrt (|x + r|) :=
            begin 
              by_cases sqrt (|x + r|) = 0,
              { rw h, simp },
              { 
                have : sqrt (|x + r|) > 0 := begin 
                apply lt_of_le_of_ne (sqrt_nonneg _), 
                symmetry,
                exact h,
                end,
                rw le_mul_iff_one_le_left this,
                { 
                  rw le_sqrt,
                  repeat {norm_num},
                },
              }
            end,
            apply le_trans _ this,
            clear this,
            rw le_sqrt (le_of_lt hM) (abs_nonneg (x + r)),
            have := abs_sub_abs_le_abs_sub r (-x),
            calc 
            M^2 ≤ |r| - |x| : le_sub_right_of_add_le hr
            ... ≤ |x + r|   : by simp at *; rw add_comm r x at this; exact this,
          }
        }
      }
    }
  }
end

lemma has_min {f : ℝ → ℝ} {hcont : continuous f} {hubdd : unbounded f} : ∃ 
x, ∀ y, f x ≤ f y := 
begin 
  specialize hubdd (max (f 0) 1) (by norm_num),
  rcases hubdd with ⟨K, K_nonneg, hK⟩,
  set interval := set.Icc (-K) K with h,
  have hnemp : interval.nonempty := begin use 0, rw h, tidy, end,
  have := is_compact.exists_forall_le (is_compact_Icc) hnemp (continuous.continuous_on hcont),
  rcases this with ⟨x, hx, hmin⟩,
  use x,
  intro y,
  by_cases y ∈ interval,
  { exact hmin y h },
  {
    replace h : K ≤ |y| := begin 
      by_contradiction h',
      push_neg at h',
      apply h,
      simp,
      rw ← abs_le,
      apply le_of_lt h', 
    end,
    specialize hK y h,
    specialize hmin 0 (by tidy),
    apply le_trans hmin (le_trans _ hK),
    exact le_max_left (f 0) 1,
  }
end

lemma sqrt_abs_is_concave : is_concave (λ x, sqrt (|x|)) :=
begin
  intros x y t ht hxy hne,
  simp at *,
  have h₁ : 0 ≤ t * sqrt (|x|) + (1 - t) * sqrt (|y|) :=
  begin
    apply add_nonneg,
    repeat {apply mul_nonneg},
    { exact le_of_lt ht.1},
    { apply sqrt_nonneg },
    { linarith },
    { apply sqrt_nonneg },
  end,
  have h₂ : sqrt (|t * x + (1 - t) * y|) ≥ 0 := by apply sqrt_nonneg,
  rw [← abs_of_nonneg h₁, ← abs_of_nonneg h₂],
  clear h₁ h₂,
  apply abs_lt_abs_of_sq_lt_sq,
  rw [add_sq, mul_pow, mul_pow, sq_sqrt, sq_sqrt, sq_sqrt],
  repeat {apply abs_nonneg},
  rw mul_pos_iff at hxy,
  have : ∀ x y, x > 0 ∧ y > 0 ∧ x ≠ y → t ^ 2 * |x| + 2 * (t * sqrt (|x|)) * ((1 - t) * sqrt (|y|)) + (1 - t) ^ 2 * |y| < |t * x + (1 - t) * y| := begin 
    rintros a b ⟨ ha, hb, hne ⟩,
    have : 0 < t*a + (1-t)*b := begin 
      apply add_pos,
      repeat {apply mul_pos},
      repeat {linarith},      
    end,
    rw [abs_of_pos ha, abs_of_pos hb, abs_of_pos this],
    clear this,
    rw [← add_zero ((1 - t)^2 * b), ← add_assoc],
    apply add_lt_of_lt_sub_left,
    ring_nf,
    have : -a + (-b + 2 * sqrt b * sqrt a) = -(a + (b - 2 * sqrt b * sqrt a)) := by ring,
    rw this,
    apply mul_pos _ ht.1,
    rw ← mul_one (a + (b - 2 * sqrt b * sqrt a)),
    nth_rewrite 0 mul_one,
    rw add_comm _ ((a + (b - 2 * sqrt b * sqrt a)) * 1),
    ring_nf,
    rw ←mul_sub,
    apply mul_pos _,
    { simp, exact ht.2 },
    {
      rw add_sub,
      simp,
      replace this : 2 * sqrt b * sqrt a = sqrt (4*a*b) := begin 
        rw [sqrt_mul, sqrt_mul],
        replace this : sqrt 4 = sqrt (2^2) := by norm_num,
        rw [this, sqrt_sq],
        ring_nf,
        norm_num,
        norm_num,
        apply mul_nonneg,
        norm_num,
        exact le_of_lt ha,
      end,
      rw this,
      replace this : a + b = sqrt ((a+b)^2) := begin 
        rw sqrt_sq,
        linarith,
      end,
      rw this,
      apply sqrt_lt_sqrt,
      {
        repeat {apply mul_nonneg},
        norm_num,
        repeat {linarith},
      },
      {
        rw [add_sq, ← add_zero (4*a*b)],
        apply add_lt_of_lt_sub_left,
        replace this : a ^ 2 + 2 * a * b + b ^ 2 - 4 * a * b = (a - b)^2 := by ring,
        rw this,
        apply sq_pos_of_ne_zero,
        rw sub_ne_zero,
        exact hne,
      }
    },
  end,
  cases hxy,
  { exact this x y ⟨ hxy.1, hxy.2, hne⟩ },
  {
    set x' := -x with hx', 
    set y' := -y with hy', 
    have hxy' : 0 < x' ∧ 0 < y' := begin 
      rw [hx', hy'],
      simp,
      exact hxy,
    end,
    have hne' : x' ≠ y' := by rw [hx', hy']; simp; exact hne,
    have h': |t * x + (1 - t) * y| = |t * x' + (1 - t) * y'| := 
    calc
      |t * x + (1 - t) * y| = | -(t * x + (1 - t) * y)| : by rw ← abs_neg
      ... = |t * (-x) + (1 - t) * (-y)| : by ring_nf
      ... = |t * x' + (1 - t) * y'|     : by rw [hx', hy'],
    rw [h', abs_of_neg hxy.1, abs_of_neg hxy.2, ← hx', ← hy'],
    nth_rewrite 0 ← abs_of_pos hxy'.1,
    nth_rewrite 1 ← abs_of_pos hxy'.1,
    nth_rewrite 0 ← abs_of_pos hxy'.2,
    nth_rewrite 1 ← abs_of_pos hxy'.2,
    exact this x' y' ⟨hxy'.1, hxy'.2, hne'⟩,
  }
end

/- Jensen's inequality for two points -/
lemma jensen {f : ℝ → ℝ} (h : is_concave f) : ∀ x y, x * y > 0 ∧ x ≠ y → f x + f y < 2 * f ((x + y)/2) :=
begin 
  rintros x y ⟨hxy,hne⟩,
  specialize h x y (1/2) (by norm_num) hxy hne,
  norm_num at h,
  rw ← @mul_lt_mul_left _ _ _ _ (2 : ℝ) (by norm_num) at h,
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_add (1 / 2) x y] at h,
  simp at h,
  rw div_eq_mul_inv,
  nth_rewrite 1 mul_comm,
  exact h,
end

lemma epsilon_little_enough (x ε : ℝ) : x ≠ 0 → ε > 0 → ε < |x| → 0 < (x + ε)*(x - ε) := 
begin
  intros hne ε_pos hle,
  rw [add_mul,  mul_sub, mul_sub],
  ring_nf,
  simp,
  apply sq_lt_sq,
  rw ← abs_of_pos ε_pos at hle,
  exact hle,
end

/- If a collection of real numbers has no zeroes, we can choose a positive epsilon little enough so that these numbers plus or minus this epsilon, stay with the same sign -/
lemma exists_epsilon_forall (s : finset ℝ) (hnemp : s.nonempty) (r : ℝ) : (∀ x y, x ∈ s → y ∈ s → x + r + (y + r) ≠ 0) → ∃ ε : ℝ, ε > 0 ∧ ∀ x y, x ∈ s → y ∈ s → 0 < (x + (r + ε) + (y + (r + ε)))*(x + (r - ε) + (y + (r - ε))) :=
begin 
  intro hs,
  set f : ℝ × ℝ → ℝ := λ x, |x.fst + r + (x.snd + r)| / 4 with hf,
  set s' : finset(ℝ) := finset.image f (finset.product s s) with hs',
  have hnemp' : s'.nonempty := begin 
    cases hnemp with x hx,
    use f (x, x),
    rw mem_image,
    use (x,x),
    tidy,
  end,
  set ε := finset.min' s' hnemp' with hε,
  have ε_pos : ε > 0 := begin 
    have := min'_mem s' hnemp',
    rw mem_image at this,
    rcases this with ⟨a, a_in, ha⟩,
    rw [hε, ← ha],
    simp [f],
    apply div_pos,
    {
        apply lt_of_le_of_ne,
        { apply abs_nonneg },
        {
          symmetry,
          intro h,
          rw abs_eq_zero at h,
          simp at a_in,
          exact hs a.fst a.snd a_in.1 a_in.2 h,
        }
      },
      { norm_num, }
  end,
  use ε,
  split,
  { exact ε_pos },
  {
    intros x y hx hy,
    have : ε ≤ |x + r + (y + r)| / 4 := begin 
      have := min'_le s',
      have hin : |x + r + (y + r)| / 4 ∈ s' := begin
        rw mem_image,
        use (x,y),
        split,
        { tidy },
        { rw hf },
      end,
      specialize this (|x + r + (y + r)| / 4) hin,
      rw hε,
      exact this,
    end,
    specialize hs x y hx hy,
    have haux : (x + (r + ε) + (y + (r + ε))) * (x + (r - ε) + (y + (r - ε))) = (x + r + (y + r) + 2*ε) * (x + r + (y + r) - 2*ε) := by ring_nf,
    rw haux, 
    apply epsilon_little_enough (x + r + (y + r)) (2*ε) hs,
    {
      apply mul_pos,
      norm_num,
      exact ε_pos,
    },
    { linarith [this] }
  }
end


/- The problem we want to solve -/

theorem problem2 (n : ℕ) : ∀ s : finset ℝ, s.card = n → ∑ x y in s, f_sub x y ≤ ∑ x y in s, f_add x y :=
begin 
  induction n using nat.two_step_induction with n hn2 hn1,
  {
    intros s hs,
    rw finset.card_eq_zero at hs,
    rw hs,
    simp,
  },
  {
    intros s hs,
    rw card_eq_one at hs,
    cases hs with r h,
    rw h,
    simp,
    apply sqrt_nonneg,
  },
  {
    intros s hs,
    have hnemp : s.nonempty := begin rw [← finset.card_pos, hs], norm_num, end,
    cases @has_min (@f_move s) (by continuity) (f_is_unbounded hnemp) with r_min hrmin,
    have := hrmin 0,
    unfold f_move at this,
    simp at this,
    apply le_trans _ this,
    clear this,
    by_cases h₁ : (∃ x : ℝ, x ∈ s ∧ x + r_min = 0),
    {
      clear hn2 hrmin,
      cases h₁ with x hx,
      set f : ℝ ↪ ℝ := begin
        refine { to_fun := λ x, x + r_min, inj' := _ },
        intros a b,
        simp,
      end with hf,
      set s' := map f (s \ {x}) with hs',
      specialize hn1 s',
      have hcard : s'.card = n.succ := begin
        have h : {x} ⊆ s := by tidy,
        rw [hs', card_map, card_sdiff h, hs],
        simp,
      end,
      specialize hn1 hcard,
      rw [sum_map', sum_map'] at hn1,
      simp at hn1,
      rw sum_union' hx.1 f_sub_comm,
      have := sum_union' hx.1 (f_add_move_comm r_min),
      simp at this,
      rw this,
      clear this,
      unfold f_add,
      simp,
      rw [← sum_f_sub_move r_min, hx.2],
      simp,
      assumption,
    },
    {
      push_neg at h₁,
      by_cases h₂ : (∃ x y : ℝ, x ∈ s ∧ y ∈ s ∧ x + r_min + (y + r_min) = 0),
      {
        clear hn1,
        rcases h₂ with ⟨x, y, hx, hy, hxy⟩,
        have hne : x ≠ y := begin 
          intro heq,
          rw heq at hxy,
          simp at hxy,
          exact h₁ y hy hxy,
        end,
        set f : ℝ ↪ ℝ := begin
        refine { to_fun := λ x, x + r_min, inj' := _ },
        intros a b,
        simp,
        end with hf,
        specialize hn2 (map f (s \ {x, y})),
        have : (map f (s \ {x, y})).card = n := begin
          rw card_map,
          have : {x,y} ⊆ s := by tidy,
          rw [card_sdiff this, hs, card_insert_of_not_mem],
          simp,
          tidy,
        end,
        specialize hn2 this,
        clear this,
        rw [sum_map', sum_map'] at hn2,
        simp at hn2,
        rw [sum_union'' x y ⟨hx, hy, hne⟩ (f_add_move_comm r_min)],
        dsimp,
        rw sum_add_to_sum_sub hxy,
        have dx : x + r_min = -(y + r_min) := eq_neg_of_add_eq_zero hxy,
        rw add_comm at hxy,
        have dy : y + r_min = -(x + r_min) := eq_neg_of_add_eq_zero hxy,
        rw sum_add_to_sum_sub hxy,
        nth_rewrite 0 dx,
        nth_rewrite 2 dy,
        rw [f_add_comm (y + r_min), add_to_sub, add_to_sub],
        unfold f_add,
        rw add_comm at hxy,
        rw hxy,
        simp [f_sub_comm],
        rw sum_union'' x y ⟨hx, hy, hne⟩ f_sub_comm,
        simp,
        apply add_le_of_le_sub_right,
        ring_nf,
        apply add_le_of_le_sub_right,
        simp,
        exact hn2,
      },
      {
        clear hn1 hn2 h₁,
        push_neg at h₂,
        exfalso,
        have hε := exists_epsilon_forall s hnemp r_min h₂,
        rcases hε with ⟨ ε, ε_pos, hε ⟩, 
        have h₃ : @f_move s (r_min + ε) + @f_move s (r_min - ε) < 2 * @f_move s r_min := begin  
          unfold f_move,
          rw [sum_add_distrib', mul_sum],
          apply sum_lt_sum_of_nonempty hnemp,
          intros x hx,
          rw mul_sum,
          apply sum_lt_sum_of_nonempty hnemp,
          intros y hy,
          have : x + (r_min + ε) + (y + (r_min + ε)) ≠ x + (r_min - ε) + (y + (r_min - ε)) := by linarith,
          replace this := jensen sqrt_abs_is_concave (x + (r_min + ε) + (y + (r_min + ε))) (x + (r_min - ε) + (y + (r_min - ε))) ⟨hε x y hx hy, this⟩,
          have haux : (x + (r_min + ε) + (y + (r_min + ε)) + (x + (r_min - ε) + (y + (r_min - ε)))) / 2 = x + r_min + (y + r_min) := by ring,
          rw haux at this,
          unfold f_add,
          exact this,
        end,
        have h₄ : @f_move s (r_min + ε) < @f_move s r_min ∨ @f_move s (r_min - ε) < @f_move s r_min := left_lt_or_right_lt_of_add_lt_two_mul h₃,
        cases h₄,
        {
          specialize hrmin (r_min + ε),
          linarith,
        },
        {
          specialize hrmin (r_min - ε),
          linarith,
        },
      }
    }
  }
end
