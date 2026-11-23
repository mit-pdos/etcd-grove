package klog_test

import (
	"testing"

	"github.com/go-logr/logr"
	"k8s.io/klog/v2"
)

// TestPrintfEmptyWithLogger: with a logger set by SetLogger (without WriteKlogBuffer), the
// printf-style functions panic on a format whose output is empty; Info("") does not
// (fixed by #272), and neither should Infof("").
func TestPrintfEmptyWithLogger(t *testing.T) {
	klog.SetLogger(logr.Discard())
	defer klog.ClearLogger()
	for name, f := range map[string]func(){
		"Info":     func() { klog.Info("") },
		"Infof":    func() { klog.Infof("") },
		"Warningf": func() { klog.Warningf("%s", "") },
		"Errorf":   func() { klog.Errorf("") },
		"V.Infof":  func() { klog.V(0).Infof("") },
	} {
		t.Run(name, func(t *testing.T) {
			defer func() {
				if r := recover(); r != nil {
					t.Errorf("%s panicked: %v", name, r)
				}
			}()
			f()
		})
	}
}
