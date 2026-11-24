package serverlib

import (
  "gryff/src/masterproto"
  "net/rpc"
  "log"
  "time"
  "net"
  "fmt"
  "net/http"
)

func Serve(rpcPort int) {
	rpc.HandleHTTP()
  log.Printf("Listening for RPCs on port %d\n", rpcPort)
	l, err := net.Listen("tcp", fmt.Sprintf(":%d", rpcPort))
	for err != nil {
		// fix (N4): listen again (the replica used to exit)
		log.Println("Error listening for RPCs:", err)
		time.Sleep(1e9)
		l, err = net.Listen("tcp", fmt.Sprintf(":%d", rpcPort))
	}

	http.Serve(l, nil)
}

func RegisterWithMaster(myAddr string, portnum int, masterAddr string) (int, []string) {
	args := &masterproto.RegisterArgs{myAddr, portnum}
	var reply masterproto.RegisterReply

	for done := false; !done; {
		mcli, err := rpc.DialHTTP("tcp", masterAddr)
		if err == nil {
			err = mcli.Call("Master.Register", args, &reply)
			if err == nil && reply.Ready == true {
				done = true
				break
			} else if err != nil {
        log.Printf("Error registering with master: %v\n", err)
      } else if !reply.Ready {
        log.Printf("Master not ready for replica registration\n")
      }
		} else {
      log.Printf("Error dialing master: %v\n", err)
    }
		time.Sleep(1e9)
	}
	return reply.ReplicaId, reply.NodeList
}

