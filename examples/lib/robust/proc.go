package robust

import (
	"io"
	"os"
	"os/exec"
	"sync/atomic"
	"syscall"
)

// A Proc is a process started on a machine (Machine.Start): the program under test, from its own
// binary, unchanged. It ends when it is killed (Kill), or on its own (a crash of the program:
// the caller learns of it by Start's onExit).
type Proc struct {
	cmd    *exec.Cmd
	exited chan struct{}
	killed atomic.Bool
}

// Start starts the program path with arguments args on m (in its namespace: `ip netns exec`,
// which execs it, so the process is the program's), with the environment variables env added to
// this process's, its standard output and error to out. onExit (if not nil) is called when it ends
// without having been killed, with Wait's error.
func (m *Machine) Start(path string, args, env []string, out io.Writer, onExit func(error)) (*Proc, error) {
	var cmd *exec.Cmd
	if m.ns == "" {
		cmd = exec.Command(path, args...)
	} else {
		cmd = exec.Command("ip", append([]string{"netns", "exec", m.ns, path}, args...)...)
	}
	cmd.Env = append(os.Environ(), env...)
	cmd.Stdout, cmd.Stderr = out, out
	// a process that starts others and dies takes them with it
	cmd.SysProcAttr = &syscall.SysProcAttr{Pdeathsig: syscall.SIGKILL}
	if err := cmd.Start(); err != nil {
		return nil, err
	}
	p := &Proc{cmd: cmd, exited: make(chan struct{})}
	go func() {
		err := cmd.Wait()
		if !p.killed.Load() && onExit != nil {
			onExit(err)
		}
		close(p.exited)
	}()
	return p, nil
}

// Kill kills the process (SIGKILL: no handler, no cleanup, at any point of its work) and waits
// for it to end.
func (p *Proc) Kill() {
	p.killed.Store(true)
	p.cmd.Process.Kill()
	<-p.exited
}

// Exited is closed when the process has ended.
func (p *Proc) Exited() <-chan struct{} { return p.exited }
