//go:build !goose

package check

// (Not translated: recover and fmt. The program the closed theorem is about calls Run, and an
// EvalError there is a panic like any other.)

import (
	"fmt"
	"strings"
)

// Check is Run with an evaluation error reported as an Error verdict (streamcheck.py's ERROR).
func Check(cfg *Config, evs []*Event) (v Verdict) {
	k := 0
	defer func() {
		if x := recover(); x != nil {
			e, ok := x.(EvalError)
			if !ok {
				panic(x)
			}
			v = Verdict{Kind: Error, K: k, Err: e.What}
		}
	}()
	c := NewChecker(cfg)
	for _, ev := range evs {
		k = c.State.I
		c.Next(ev)
		if c.Done {
			break
		}
	}
	return c.End()
}

// String is the verdict as streamcheck.py prints it (without the event of a rejection).
func (v Verdict) String() string {
	switch v.Kind {
	case Accepted:
		return fmt.Sprintf("ACCEPTED %d", v.K)
	case Rejected:
		return fmt.Sprintf("REJECTED %d", v.K)
	case Violated:
		return fmt.Sprintf("VIOLATED %d %s", v.K, strings.Join(v.Names, ","))
	}
	return fmt.Sprintf("ERROR at event %d: %s", v.K, v.Err)
}
