import ExeterDemo.Lib

-- Proof term, used by Frédéric Tran Minh in Grenoble for instance

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦ (hf ε ε_pos).elim
   fun δ ⟨δ_pos, hδ⟩ ↦ (hu δ δ_pos).elim
     fun N hN ↦ ⟨N, fun n n_ge ↦ hδ (u n) <| hN n n_ge⟩

-- Traditional tactic proof, including backward reasonning
-- Main benefit: tactic state

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  intro ε ε_pos
  rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩
  rcases hu δ δ_pos with ⟨N, hN⟩
  use N
  intro n n_ge
  apply hδ
  apply hN
  exact n_ge

-- First verbose version. Goal: easier transfer to paper

Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  By hf applied to ε using that ε > 0 we get δ such that
    δ_pos : δ > 0 and hδ : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε
  By hu applied to δ using δ_pos we get N such that hN : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  By hδ applied to u n it suffices to prove |u n - x₀| ≤ δ
  We conclude by hN applied to n using n_ge
QED

-- A version that does not refer to assumption names

Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  Since f is continuous at x₀ and ε > 0 we get δ such that
    δ_pos : δ > 0 and hδ : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε
  Since u converges to x₀ and δ > 0 we get N such that hN : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε it suffices to prove that |u n - x₀| ≤ δ
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we conclude that |u n - x₀| ≤ δ
QED

-- A version that does not refer to assumption names and uses only forward reasonning

Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  Since f is continuous at x₀ and ε > 0 we get δ such that
    δ_pos : δ > 0 and hδ : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε
  Since u converges to x₀ and δ > 0 we get N such that hN : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we get h : |u n - x₀| ≤ δ
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε and |u n - x₀| ≤ δ
    we conclude that |f (u n) - f x₀| ≤ ε
QED

-- *** There are three assistance mode: bare, help, widget

-- Let us now see a more complicated example

Example "The squeeze theorem."
  Given: (u v w : ℕ → ℝ) (l : ℝ)
  Assume: (hu : u converges to l) (hw : w converges to l)
    (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n)
  Conclusion: v converges to l
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |v n - l| ≤ ε
  Fix ε > 0
  Since u converges to l and ε > 0 we get N such that hN : ∀ n ≥ N, |u n - l| ≤ ε
  Since w converges to l and ε > 0 we get N' such that hN' : ∀ n ≥ N', |w n - l| ≤ ε
  Let's prove that max N N' works : ∀ n ≥ max N N', |v n - l| ≤ ε
  Fix n ≥ max N N'
  Since n ≥ max N N' we get hn : n ≥ N and hn' : n ≥ N'
  Since ∀ n ≥ N, |u n - l| ≤ ε and n ≥ N we get
   hNl : -ε ≤ u n - l and hNd : u n - l ≤ ε
  Since ∀ n ≥ N', |w n - l| ≤ ε and n ≥ N' we get
    hN'l : -ε ≤ w n - l and hN'd : w n - l ≤ ε
  Let's prove that |v n - l| ≤ ε
  Let's first prove that -ε ≤ v n - l
  Calc -ε ≤ u n - l by assumption
      _   ≤ v n - l since u n ≤ v n
  Let's now prove that v n - l ≤ ε
  Calc v n - l ≤ w n - l  since v n ≤ w n
      _        ≤ ε        by assumption
QED
