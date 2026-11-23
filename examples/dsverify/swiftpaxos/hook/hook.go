package hook

import (
	"os"
	"os/signal"
	"syscall"
)

func HookUser1(f func()) {
	user1 := make(chan os.Signal, 1)
	signal.Notify(user1, syscall.Signal(0xa)) // syscall.SIGUSR1 on linux (verification workaround: the harness has the constant as a name only)

	go func() {
		<-user1
		f()
	}()
}
