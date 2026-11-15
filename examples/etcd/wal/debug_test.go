package wal

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/wal/crashtest/walref"
)

func fmtOps(h []walOp) string {
	s := ""
	for _, o := range h {
		if o.snap {
			s += fmt.Sprintf("snap%d@%d ", o.idx, o.term)
			continue
		}
		s += "save("
		for _, e := range o.ents {
			s += fmt.Sprintf("e%d@%d/%x ", e.index, e.term, e.salt&0xffff)
		}
		s += fmt.Sprintf("hs%d/%d/%d) ", o.hs.term, o.hs.vote, o.hs.commit)
	}
	return s
}

func fmtC(c contents) string {
	s := fmt.Sprintf("base %d@%d hs %d/%d/%d ents ", c.baseIdx, c.baseTerm, c.hs.term, c.hs.vote, c.hs.commit)
	for _, e := range c.ents {
		s += fmt.Sprintf("e%d@%d/%x(%d) ", e.index, e.term, e.salt&0xffff, e.size)
	}
	return s
}

// TestDebugImage: WALROBUST_IMAGE=<kept image> explains a violation.
func TestDebugImage(t *testing.T) {
	img := os.Getenv("WALROBUST_IMAGE")
	if img == "" {
		t.Skip()
	}
	tmp := t.TempDir()
	exec.Command("cp", "-a", img, tmp+"/r").Run()
	root := tmp + "/r"
	o := loadOracle(root + "/oracle/state")
	d := walref.DecodeDir(filepath.Join(root, "data/member/wal"))
	t.Logf("decoded (end %s, purged %v, files %v):", d.End, d.Purged, d.Files)
	s := ""
	for _, r := range d.Recs {
		s += r.String() + " "
	}
	t.Log(s)
	st, c, _ := restartRead(zap.NewNop(), root+"/data/member/wal", nil)
	t.Logf("read %d: %s", st, fmtC(c))
	t.Logf("since (synced %d): %s", o.synced, fmtOps(o.since))
	for i, cd := range o.cands {
		t.Logf("cand %d (len %d, unl %d, pur %d): %s", i, len(cd.h), cd.unl, cd.pur, fmtOps(cd.h))
		h := append(copyOps(cd.h), o.since...)
		for _, im := range walImgs(h, len(cd.h)+int(o.synced)) {
			rc, ok := walRead(im)
			t.Logf("  img len %d ok %v: %s", len(im), ok, fmtC(rc))
		}
	}
}
