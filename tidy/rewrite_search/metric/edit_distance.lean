import tidy.rewrite_search.core

import data.rat

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

namespace tidy.rewrite_search.edit_distance

variables {α : Type} [decidable_eq α]

@[derive decidable_eq]
structure ed_partial :=
  (prefix_length : ℚ)
  (suffix    : list table_ref)
  (distances : list ℚ) -- distances from the prefix of l₁ to each non-empty prefix of l₂

def get_weight (weights : table ℚ) (r : table_ref) : ℚ := max (weights.iget r) 1

def compute_initial_distances_aux (weights : table ℚ) : ℚ → list table_ref → list ℚ
| _ [] := []
| so_far (a :: rest) :=
  let so_far := so_far + (get_weight weights a) in
  list.cons so_far (compute_initial_distances_aux so_far rest)

def compute_initial_distances (weights : table ℚ) (l : list table_ref) : list ℚ :=
  compute_initial_distances_aux weights 0 l

def empty_partial_edit_distance_data (weights : table ℚ) (l₁ l₂ : list table_ref) : ed_partial :=
  ⟨ 0, l₁, compute_initial_distances weights l₂ ⟩

def triples {α : Type} (p : ed_partial) (l₂ : list α): list (ℚ × ℚ × α) :=
p.distances.zip ((list.cons p.prefix_length p.distances).zip l₂)

universe u

def minl {α : Type u} [inhabited α] [decidable_linear_order α] : list α → α
| [] := default α
| [a] := a
| (n :: rest) := min n (minl rest)

--TODO explain me
meta def fold_fn (weights : table ℚ) (h : table_ref) (n : ℚ × list ℚ) : ℚ × ℚ × table_ref → ℚ × list ℚ
| (a, b, r) :=
  let m := if h = r then b else minl [
    /- deletion     -/ a + (get_weight weights r),
    /- substitution -/ b + max (get_weight weights r) (get_weight weights h),
    /- insertion    -/ n.2.head + (get_weight weights h)
  ] in (min m n.1, list.cons m n.2)

--TODO explain me
meta def improve_bound_once (weights : table ℚ) (l r : list table_ref) (cur : ℚ) (p : ed_partial) : bound_progress ed_partial :=
  match p.suffix with
    | [] := exactly p.distances.ilast p
    | (h :: t) :=
      let new_prefix_length := p.prefix_length + (get_weight weights h) in
      let initial : ℚ × list ℚ := (new_prefix_length, [new_prefix_length]) in
      let new_distances : ℚ × list ℚ := (triples p r).foldl (fold_fn weights h) initial in
      at_least new_distances.1 ⟨ new_prefix_length, t, new_distances.2.reverse.drop 1 ⟩
  end

meta def improve_bound_over (weights : table ℚ) (l r : list table_ref) (m : ℚ) : bound_progress ed_partial → bound_progress ed_partial
| (exactly n p) := exactly n p
| (at_least n p) :=
  if n > m then
    at_least n p
  else
    improve_bound_over (improve_bound_once weights l r n p)

end tidy.rewrite_search.edit_distance

namespace tidy.rewrite_search.metric.edit_distance

open tidy.rewrite_search.edit_distance

structure ed_config :=
(refresh_freq     : ℕ := 10)
(explain_thoughts : bool := ff)
(trace_weights    : bool := ff)

structure ed_state :=
  (weights : table ℚ)
def ed_state.init : ed_state := ⟨table.create⟩

-- In future we might allow init_fn to return some internal weight state. At
-- the moment, it is just used to ensure that an external depedency (e.g.
-- external program or custom lean fork) is present.
meta def calc_weights_fn (α δ : Type) := ed_config → search_state α ed_state ed_partial δ → tactic (table ℚ)

meta structure ed_weight (α δ : Type) :=
(init : init_fn unit)
(calc_weights : calc_weights_fn α δ)

meta def ed_weight_constructor := Π α δ, ed_weight α δ

variables {α δ : Type} (g : search_state α ed_state ed_partial δ) (conf : ed_config)

meta def ed_init (weight_init : init_fn unit) : tactic (init_result ed_state) := do
  init_result.chain "weight" weight_init $ λ _,
    init_result.pure ed_state.init

meta def ed_init_bound (l r : vertex) : bound_progress ed_partial :=
  at_least 0 (empty_partial_edit_distance_data g.metric_state.weights l.tokens r.tokens)

meta def ed_reweight (fn : search_state α ed_state ed_partial δ → tactic (table ℚ)) (g : search_state α ed_state ed_partial δ) : tactic (search_state α ed_state ed_partial δ) := do
  g ← g.reset_all_estimates ed_init_bound,
  weights ← fn g,
  if conf.trace_weights then
    let weight_pairs := (g.tokens.to_list.zip weights.to_list).map (
      λ p : token × ℚ, to_string format!"{p.1.str}={p.2}"
    ) in
    tactic.trace format!"reweighted: {weight_pairs}"
  else
    tactic.skip,
  return $ g.mutate_metric ⟨weights⟩

meta def ed_update (fn : search_state α ed_state ed_partial δ → tactic (table ℚ)) (g : search_state α ed_state ed_partial δ) (itr : ℕ) : tactic (search_state α ed_state ed_partial δ) :=
  if conf.refresh_freq > 0 ∧ (itr % (conf.refresh_freq + 1) = 0) then do
    if conf.explain_thoughts then tactic.trace "pause! refreshing weights..." else tactic.skip,
    ed_reweight conf fn g
  else
    return g

meta def ed_improve_estimate_over (m : ℚ) (l r : vertex) (bnd : bound_progress ed_partial) : bound_progress ed_partial :=
  improve_bound_over g.metric_state.weights l.tokens r.tokens m bnd

end tidy.rewrite_search.metric.edit_distance

namespace tidy.rewrite_search.metric
open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance

meta def weight.none : ed_weight_constructor :=
  λ α δ, ⟨init_result.pure (), λ conf g, return table.create⟩

meta def edit_distance (conf : ed_config := {}) (w_cons : ed_weight_constructor := weight.none) : metric_constructor ed_state ed_partial :=
  λ α δ, let w := w_cons α δ in
  ⟨ ed_init w.init, ed_update conf $ w.calc_weights conf, ed_init_bound, ed_improve_estimate_over ⟩

end tidy.rewrite_search.metric