/- Review check (fs-final): the axioms of the example theorems.
Run: `lake env lean notes/axiom-review/fs-final/Axioms.lean`. -/
import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Results
import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.Results
import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Results
import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLogResults
import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DirSwapResults
import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Link

#print axioms Perennial.EtcdGrove.osfs_bboltfs.bootCrashSafety
#print axioms Perennial.EtcdGrove.osfs_crashlog.crash_safety
#print axioms Perennial.EtcdGrove.osfs_walfs.crash_safety
#print axioms Perennial.EtcdGrove.osfs_walfs.seglog_crash_safety
#print axioms Perennial.EtcdGrove.osfs_walfs.dirswap_crash_safety
