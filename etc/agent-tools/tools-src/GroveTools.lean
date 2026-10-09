/-
Umbrella module for the proof tools: `import GroveTools` gives
- `Tools.CompactGoals`: compact goal printing (display only);
- `BtreeLib.ListAuto`: `list_seg`, `sorted_seg` and the `seg_*` slice-shape lemmas;
- `GroveTactics`: `wp_bounds`, `wp_load_frac`/`wp_auto_frac`, `wp_run`, `wp_ptr_method`,
  `inorm`/`iframe_norm`, `timed`.
-/
import Tools.CompactGoals
import BtreeLib.ListAuto
import GroveTactics
