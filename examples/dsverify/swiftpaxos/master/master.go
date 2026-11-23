package master

import (
	"errors"
	"fmt"
	"net"
	"net/http"
	"net/rpc"
	"sync"
	"time"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

type Master struct {
	*dlog.Logger

	N          int
	port       int
	nodeList   []string
	addrList   []string
	portList   []int
	lock       *sync.Mutex
	nodes      []*rpc.Client
	leader     []bool
	alive      []bool
	latencies  []float64
	finishInit bool
	initCond   *sync.Cond
	nextLeader int
	config     *config.Config
}

func New(N, port int, config *config.Config, logger *dlog.Logger) *Master {
	master := &Master{
		Logger: logger,

		N:          N,
		port:       port,
		nodeList:   make([]string, 0, N),
		addrList:   make([]string, 0, N),
		portList:   make([]int, 0, N),
		lock:       new(sync.Mutex),
		nodes:      make([]*rpc.Client, N),
		leader:     make([]bool, N),
		alive:      make([]bool, N),
		latencies:  make([]float64, N),
		finishInit: false,
		nextLeader: -1,
		config:     config,
	}
	master.initCond = sync.NewCond(master.lock)
	return master
}

func (master *Master) Run() {
	master.Printf("master starting on port %d", master.port)
	master.Printf("waiting for %d replicas", master.N)

	if err := rpc.Register(master); err != nil {
		// Verification workaround: rpc.Register of a fresh *Master cannot fail in Go (it has
		// exported methods, and the name "Master" is registered once per process); the lab's
		// rpc model's spec allows a failure, so on one, do as Fatal intends: do not serve.
		master.Fatal("master register error:", err)
		for {
			time.Sleep(time.Second)
		}
	}
	rpc.HandleHTTP()
	l, err := net.Listen("tcp", fmt.Sprintf(":%d", master.port))
	for err != nil {
		master.Fatal("master listen error:", err)
		// Fatal returns with a non-verbose logger: do not serve a nil
		// listener, listen again.
		time.Sleep(time.Second)
		l, err = net.Listen("tcp", fmt.Sprintf(":%d", master.port))
	}
	go master.run()
	http.Serve(l, nil)
}

func (master *Master) run() {
	for {
		master.lock.Lock()
		if len(master.nodeList) == master.N {
			master.lock.Unlock()
			break
		}
		master.lock.Unlock()
		time.Sleep(time.Second)
	}
	time.Sleep(2 * time.Second)

	for i := 0; i < master.N; {
		var err error
		addr := fmt.Sprintf("%s:%d", master.addrList[i], master.portList[i]+1000)
		master.nodes[i], err = rpc.DialHTTP("tcp", addr)
		if err != nil {
			master.Printf("error connecting to replica %d (%v), retrying...", i, addr)
			time.Sleep(time.Second)
		} else {
			btlReply := defs.NewBeTheLeaderReply()
			master.lock.Lock() // M1: leader is shared with the rpc methods
			isLeader := master.leader[i]
			master.lock.Unlock()
			if isLeader {
				err = master.nodes[i].Call("Replica.BeTheLeader", &defs.BeTheLeaderArgs{}, btlReply)
				if err != nil {
					master.Fatal("Not today Zurg!")
					// Model adaptation: Fatal returns with a non-verbose logger; a failed
					// call's reply is not a reply (the lab's rpc model lets a failed Call leave
					// any value in it): use the initial reply (Leader and NextLeader -1), as
					// Go's net/rpc leaves it when the call fails before its reply is decoded.
					btlReply = defs.NewBeTheLeaderReply()
				}
				defs.UpdateBeTheLeaderReply(btlReply)
				leaderI := i
				if btlReply.Leader != -1 {
					leaderI = int(btlReply.Leader)
					master.lock.Lock()
					master.leader[i] = false
					master.leader[leaderI] = true
					master.lock.Unlock()
				}
				master.nextLeader = int(btlReply.NextLeader)
				if leaderI == i {
					master.Printf("replica %d is the new leader", leaderI)
				} else if leaderI < i {
					i = leaderI - 1
				}
			}
			i++
		}
	}

	var new_leader bool
	pingNode := func(i int, node *rpc.Client) {
		err := node.Call("Replica.Ping", &defs.PingArgs{}, &defs.PingReply{})
		// M1: alive and leader are shared with the rpc methods
		master.lock.Lock()
		defer master.lock.Unlock()
		if err != nil {
			master.alive[i] = false
			if master.leader[i] {
				new_leader = true
				master.leader[i] = false
			}
		} else {
			master.alive[i] = true
		}
	}
	for i, node := range master.nodes {
		pingNode(i, node)
	}
	master.lock.Lock()
	// initialization is finished
	// (i.e., `alive` has been computed)
	master.finishInit = true
	master.initCond.Broadcast()
	master.lock.Unlock()

	beTheLeader := func(i int) error {
		master.lock.Lock() // M1: alive and leader are shared with the rpc methods
		alive := master.alive[i]
		master.lock.Unlock()
		if alive {
			btlReply := defs.NewBeTheLeaderReply()
			err := master.nodes[i].Call("Replica.BeTheLeader", &defs.BeTheLeaderArgs{}, btlReply)
			if err == nil {
				defs.UpdateBeTheLeaderReply(btlReply)
				leaderI := i
				if btlReply.Leader != -1 {
					// TODO: need to set leader[old_leader] to false?
					leaderI = int(btlReply.Leader)
				}
				master.lock.Lock()
				master.leader[leaderI] = true
				master.lock.Unlock()
				master.nextLeader = int(btlReply.NextLeader)
				master.Printf("replica %d is the new leader", leaderI)
				return nil
			}
			return err
		}
		return errors.New("dead")
	}

	for {
		time.Sleep(3 * time.Second)
		new_leader = false
		for i, node := range master.nodes {
			pingNode(i, node)
		}

		if !new_leader {
			continue
		}
		if master.nextLeader != -1 {
			if beTheLeader(master.nextLeader) == nil {
				continue
			}
		}
		for i := range master.nodes {
			if beTheLeader(i) == nil {
				break
			}
		}
	}
}

func (master *Master) Register(args *defs.RegisterArgs, reply *defs.RegisterReply) error {
	master.lock.Lock()
	defer master.lock.Unlock()

	nlen := len(master.nodeList)
	index := nlen

	addrPort := fmt.Sprintf("%s:%d", args.Addr, args.Port)

	for i, ap := range master.nodeList {
		if addrPort == ap {
			index = i
			break
		}
	}

	if index == nlen {
		master.nodeList = master.nodeList[0 : nlen+1]
		master.nodeList[nlen] = addrPort
		master.addrList = master.addrList[0 : nlen+1]
		master.addrList[nlen] = args.Addr
		master.portList = master.portList[0 : nlen+1]
		master.portList[nlen] = args.Port
		master.leader[index] = false
		nlen++

		// Model adaptation (X1): no `ping` (os/exec, strconv.ParseFloat); every
		// replica gets the same fixed latency, so the selection below picks the
		// first registered replica (index 0) as the first leader.
		master.latencies[index] = 0
		master.Printf("node %v [%v] -> %v", index,
			master.nodeList[index], master.latencies[index])
	}

	if nlen == master.N {
		reply.Ready = true
		reply.ReplicaId = index
		reply.NodeList = master.nodeList
		reply.IsLeader = false

		minLatency := 1.7976931348623157e308 // math.MaxFloat64 (verification workaround: Perennial has the constant as a name only)
		leader := -1

		if master.config.Leader != nil {
			if addrPort == *master.config.Leader {
				leader = index
			}
		} else {
			for i := 0; i < len(master.leader); i++ {
				if master.latencies[i] < minLatency {
					minLatency = master.latencies[i]
					leader = i
				}
			}
		}

		if leader == index {
			master.leader[index] = true
			reply.IsLeader = true
		}

	} else {
		reply.Ready = false
	}

	return nil
}

func (master *Master) GetLeader(args *defs.GetLeaderArgs, reply *defs.GetLeaderReply) error {
	master.lock.Lock()
	defer master.lock.Unlock()

	for i, l := range master.leader {
		if l {
			*reply = defs.GetLeaderReply{
				LeaderId: i,
			}
			break
		}
	}
	return nil
}

func (master *Master) GetReplicaList(args *defs.GetReplicaListArgs, reply *defs.GetReplicaListReply) error {
	master.lock.Lock()

	for !master.finishInit {
		master.initCond.Wait()
	}

	if len(master.nodeList) == master.N {
		reply.Ready = true
	} else {
		reply.Ready = false
	}

	reply.ReplicaList = make([]string, 0)
	reply.AliveList = make([]bool, 0)
	for i, node := range master.nodeList {
		reply.ReplicaList = append(reply.ReplicaList, node)
		reply.AliveList = append(reply.AliveList, master.alive[i])
	}

	master.Printf("nodes list %v", reply.ReplicaList)
	master.lock.Unlock()
	return nil
}
