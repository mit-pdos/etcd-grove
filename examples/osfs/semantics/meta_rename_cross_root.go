//go:build linux

package semantics

import (
	"os"
	"sync"
)

// A rename across roots is outside the model (proposed model decision, WAL link
// L4, notes/wal-link-l4-fsext.md; pending review, not yet in Impl.lean).
//
// Decision: the Rename step is stuck unless its source and target are in one
// root's tree (OsState.SameRoot s t). With that, the path a call records at
// CallBegin (Rename's source) names the only root its walks touch, and a
// directory rename is stuck only while another call in that root's tree is in
// flight (meta_dir_rename_stuck.go).
//
// Lean (proposed): Impl.lean: OsState.SameRoot; the Rename step's conjunct
// `st.SameRoot s t`; ProcState.calls recording the call's path.
//
// Excluded (stuck): the rename below, whose target walks root A's tree while
// A's thread moves directories on that path.
//
// Why: measured (meta_rename_scoped_test.go, TestCrossRootRenameExcluded; the
// independent attack, /shared/tmp/l4-attack/race: 296 of 20000 at depth 1900 on
// ext4): rename(C/f, A/p/<chain>/q/g) succeeds although A/p/<chain>/q exists in
// no tree of the log (A moves p to z, then q into z/<chain>): rename(2) walks
// its target's path too, and a walk validates only each parent's d_seq as it
// steps. etcd never renames across directories of different members (wal's cut
// and Create rename within one WAL directory and its parent).
func CrossRootRename(dir string) {
	os.MkdirAll(dir+"/A/p/s/s", 0o755)
	os.MkdirAll(dir+"/A/w/q", 0o755)
	os.MkdirAll(dir+"/C", 0o755)
	f, _ := os.Create(dir + "/C/f")
	f.Close()
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		os.Rename(dir+"/C/f", dir+"/A/p/s/s/q/g") // stuck in the model: C and A differ
		wg.Done()
	}()
	os.Rename(dir+"/A/p", dir+"/A/z")
	os.Rename(dir+"/A/w/q", dir+"/A/z/s/s/q")
	wg.Wait()
	// Linux: the first rename may succeed, g at A/z/s/s/q/g, a path A/p/s/s/q never had
}
