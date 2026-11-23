package gryff

import (
	//    "state"
	"gryff/src/epaxosproto"
	"sort"
	"time"
  "gryff/src/dlog"
  "gryff/src/gryffproto"
)

const (
	WHITE int8 = iota
	GRAY
	BLACK
)

type Exec struct {
	r *EPaxosRMWHandler
}

type SCComponent struct {
	nodes []*Instance
	color int8
}

func (e *Exec) executeCommand(replica int32, instance int32) bool {
	if e.r.InstanceSpace[replica][instance] == nil {
		return false
	}
	inst := e.r.InstanceSpace[replica][instance]
	if inst.Status == epaxosproto.EXECUTED {
		return true
	}
	if inst.Status != epaxosproto.COMMITTED {
		return false
	}

  dlog.Printf("[%d.%d] Finding scc and then executing.\n", replica, instance)
	if !e.findSCC(inst) {
		return false
	}

	return true
}

var stack []*Instance = make([]*Instance, 0, 100)

func (e *Exec) findSCC(root *Instance) bool {
	index := 1
	//find SCCs using Tarjan's algorithm
	stack = stack[0:0]
	return e.strongconnect(root, &index)
}

func (e *Exec) strongconnect(v *Instance, index *int) bool {
  dlog.Printf("[%d] SCC %d %d.\n", e.r.R.Id, v.Slot, v.Seq)
	v.Index = *index
	v.Lowlink = *index
	*index = *index + 1

	l := len(stack)
	if l == cap(stack) {
		newSlice := make([]*Instance, l, 2*l)
		copy(newSlice, stack)
		stack = newSlice
	}
	stack = stack[0 : l+1]
	stack[l] = v

	for q := int32(0); q < int32(e.r.R.N); q++ {
		inst := v.Deps[q]
		for i := e.r.ExecedUpTo[q] + 1; i <= inst; i++ {
			for e.r.InstanceSpace[q][i] == nil || e.r.InstanceSpace[q][i].Cmds == nil || v.Cmds == nil {
        if v.lb != nil && v.lb.blockStartTime.IsZero() {
          v.lb.blockStartTime = time.Now()
        }
        dlog.Printf("Waiting for dep %d.%d predecessor %d.%d to exist.\n", q, inst, q, i)
				e.r.R.mtx.Unlock() // fix (G2): release the replica's lock while waiting
				time.Sleep(1000 * 1000)
				e.r.R.mtx.Lock()
			}
			/*        if !state.Conflict(v.Command, e.r.InstanceSpace[q][i].Command) {
			          continue
			          }
			*/
			if e.r.InstanceSpace[q][i].Status == epaxosproto.EXECUTED {
				continue
			}
			for e.r.InstanceSpace[q][i].Status != epaxosproto.COMMITTED {
        if v.lb != nil && v.lb.blockStartTime.IsZero() {
          v.lb.blockStartTime = time.Now()
        }
        dlog.Printf("Waiting for dep %d.%d predecessor %d.%d to be committed.\n", q, inst, q, i)
				e.r.R.mtx.Unlock() // fix (G2): release the replica's lock while waiting
				time.Sleep(1000 * 1000)
				e.r.R.mtx.Lock()
			}
			w := e.r.InstanceSpace[q][i]

			if w.Index == 0 {
				//e.strongconnect(w, index)
				if !e.strongconnect(w, index) {
					for j := l; j < len(stack); j++ {
						stack[j].Index = 0
					}
					stack = stack[0:l]
					return false
				}
				if w.Lowlink < v.Lowlink {
					v.Lowlink = w.Lowlink
				}
			} else { //if e.inStack(w)  //<- probably unnecessary condition, saves a linear search
				if w.Index < v.Lowlink {
					v.Lowlink = w.Index
				}
			}
		}
	}

	if v.Lowlink == v.Index {
		//found SCC
		list := stack[l:len(stack)]

    dlog.Printf("SCC size: %d.\n", len(list))

		//execute commands in the increasing order of the Seq field
		sort.Sort(nodeArray(list))
		for _, w := range list {
			for w.Cmds == nil {
				e.r.R.mtx.Unlock() // fix (G2): release the replica's lock while waiting
				time.Sleep(1000 * 1000)
				e.r.R.mtx.Lock()
			}
      if w.lb != nil {
        w.lb.executedTime = time.Now()
        blocked := int64(0)
        if !w.lb.blockStartTime.IsZero() {
          blocked = int64(w.lb.executedTime.Sub(w.lb.blockStartTime))
        }
        dlog.Printf("[%d.%d] Execute delay: %d (blocked %d).\n", e.r.R.Id, w.Slot, w.lb.executedTime.Sub(w.lb.committedTime), blocked)
      }

      // fix (G44): a committed no-op (no command) executes nothing (EPaxos's executor executes
      // each of an instance's commands; Gryff's RMW executor reads the first)
      if len(w.Cmds) > 0 {
        var vt gryffproto.ValTag
        pvt, ok := e.r.PrevValTag[w.Cmds[0].K]
        if !ok || w.Base.T.GreaterThan(pvt.T) {
          vt.V = w.Base.V
          gooseCopy0 := w.Base.T // verification workaround (T1): copy through a local
          vt.T = gooseCopy0
        } else {
          vt.V = pvt.V
          gooseCopy1 := pvt.T // verification workaround (T1): copy through a local
          vt.T = gooseCopy1
        }
        // do cas
        if w.Cmds[0].OldValue == vt.V {
          vt.V = w.Cmds[0].V
        }
        // fix (G1): the result of an rmw applied to the value with carstamp (ts, id, rmwc) has
        // carstamp (ts, id, rmwc + 1), and it is the value the next rmw on the key applies to
        // when its own base is older (Gryff's rmw carstamp rule; the SDP handler applies it too:
        // sdprmwhandler.go, Tag{maxValTag.T.Ts, maxValTag.T.Cid, maxValTag.T.Rmwc + 1})
        vt.T.Rmwc++
        e.r.PrevValTag[w.Cmds[0].K] = vt
        // avoid concurrency bugs by performing overwrite in "main" goroutine
        e.r.executeOverwriteChan <- &ExecuteOverwrite{w.Cmds[0].K, vt.V, &vt.T, w.Leader, w.Slot}
      }
      // never do the below:
      //  e.r.R.HandleOverwrite(w.Cmds[0].K, vt.V, &vt.T)

			/*for idx := 0; idx < len(w.Cmds); idx++ {
        if w.lb != nil {
          dlog.Printf("[%d.%d] Executing command %d.\n", e.r.R.Id, w.Slot, idx)
        }
				val := w.Cmds[idx].Execute(e.r.R.State)
				if e.r.R.NeedsWaitForExecute(&w.Cmds[idx]) && w.lb != nil && w.lb.clientProposals != nil {
					e.r.R.ReplyProposeTS(
						&genericsmrproto.ProposeReplyTS{
							TRUE,
							w.lb.clientProposals[idx].CommandId,
							val,
							w.lb.clientProposals[idx].Timestamp},
						w.lb.clientProposals[idx].Reply)
				}
			}*/
      dlog.Printf("[%d.%d] Executed in scc.\n", w.Leader, w.Slot)
			w.Status = epaxosproto.EXECUTED
		}
		stack = stack[0:l]
	}
	return true
}

func (e *Exec) inStack(w *Instance) bool {
	for _, u := range stack {
		if w == u {
			return true
		}
	}
	return false
}

type nodeArray []*Instance

func (na nodeArray) Len() int {
	return len(na)
}

func (na nodeArray) Less(i, j int) bool {
	// fix (G4): a total order, so that every replica executes a component's instances in the
	// same order whatever order its search pushed them in (sort.Sort is not stable): Seq, then
	// the instance's id (leader, slot), which is unique
	if na[i].Seq != na[j].Seq {
		return na[i].Seq < na[j].Seq
	}
	if na[i].Leader != na[j].Leader {
		return na[i].Leader < na[j].Leader
	}
	return na[i].Slot < na[j].Slot
}

func (na nodeArray) Swap(i, j int) {
	na[i], na[j] = na[j], na[i]
}
