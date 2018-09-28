import tidy.rewrite_search.core

open tidy.rewrite_search

namespace tidy.rewrite_search.tracer.unit

open tactic

meta def unit_tracer_init : tactic (init_result unit) := init_result.pure ()
meta def unit_tracer_publish_vertex (_ : unit) (_ : vertex) : tactic unit := skip
meta def unit_tracer_publish_edge (_ : unit) (_ : edge) : tactic unit := skip
meta def unit_tracer_publish_visited (_ : unit) (_ : vertex) : tactic unit := skip
meta def unit_tracer_publish_finished (_ : unit) (_ : list edge) : tactic unit := skip
meta def unit_tracer_dump (_ : unit) (_ : string) : tactic unit := skip
meta def unit_tracer_pause (_ : unit) : tactic unit := skip

end tidy.rewrite_search.tracer.unit

namespace tidy.rewrite_search.tracer

open tidy.rewrite_search.tracer.unit

meta def unit_tracer : tracer_constructor unit := λ α β γ,
  tracer.mk α β γ unit_tracer_init unit_tracer_publish_vertex unit_tracer_publish_edge unit_tracer_publish_visited unit_tracer_publish_finished unit_tracer_dump unit_tracer_pause

meta def no {δ : Type} (_ : tracer_constructor δ) : tracer_constructor unit := unit_tracer

end tidy.rewrite_search.tracer