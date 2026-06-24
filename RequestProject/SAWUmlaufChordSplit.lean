import RequestProject.SAWUmlaufPolygon

/-!
# Interior-diagonal split: reusable simplicity brick (relocated)

The reusable combinatorial bricks for the **interior-diagonal split** of a
simple polygon (`pathEdges`, `closedEdges_eq_pathEdges`,
`mem_closedEdges_of_mem_pathEdges`, `PolygonSimple_of_simplePath`,
`polyCycNondeg_of_path`) used to live here.  They have been **moved into**
`RequestProject.SAWUmlaufPolygon` (just before the open Meisters two-ears
branches) so that those branches — `meisters_reduction_interior2` and the
bad-diagonal subcase of `meisters_reduction_empty2` — can actually consume
them.  Previously they were stranded downstream of `SAWUmlaufPolygon` (which
this file imports), hence unusable where they were needed.

This file is kept (and still imported by `RequestProject.SAWFinal`) only to
preserve the build chain and document the relocation; all of its former content
now lives upstream in `SAWUmlaufPolygon`.
-/
