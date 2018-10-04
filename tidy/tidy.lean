-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic.basic
import tactic.tidy
import .backwards_reasoning
import .forwards_reasoning
import .rewrite_search
import .rewrite_search.tracer
import .luxembourg_chain
import category_theory.category
import tidy.lib.tactic

open tactic

meta def weak_tidy_tactics : list (tactic string) := [
  reflexivity                                 >> pure "refl",
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  propositional_goal >> assumption            >> pure "assumption",
  backwards_reasoning,
  `[ext1]                                     >> pure "ext1",
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  fsplit                                      >> pure "fsplit",
  injections_and_clear                        >> pure "injections_and_clear",
  terminal_goal >> (`[solve_by_elim])         >> pure "solve_by_elim",
  forwards_reasoning,
  propositional_goal >> forwards_library_reasoning,
  `[unfold_aux]                               >> pure "unfold_aux"
]

meta def extended_tidy_tactics : list (tactic string) := [
  tactic.interactive.rewrite_search,
  tidy.run_tactics
]

@[obviously] meta def obviously_1 := tidy { tactics := weak_tidy_tactics ++ extended_tidy_tactics }

namespace tactic.interactive

meta def weak_tidy := tidy { tactics := weak_tidy_tactics }

open tidy.rewrite_search

meta def qed {α β γ δ : Type} (rs : interactive.parse (optional rw_rules)) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit := do
  let srch := all_goals (match rs with
  | none    := rewrite_search cfg
  | some rs := rewrite_search_with rs cfg
  end >> return ()),
  if_not_done (try srch) $
  if_not_done (try weak_tidy) $
  srch

meta def hammer {α β γ δ : Type} (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit := do
  if_not_done (all_goals (try $ simp_search cfg)) $
  if_not_done (try weak_tidy) $
  if_not_done (all_goals (try $ simp_search cfg)) $
  all_goals (rewrite_search cfg >> return ())

notation `□` := by qed []
notation `□!` := by hammer

end tactic.interactive