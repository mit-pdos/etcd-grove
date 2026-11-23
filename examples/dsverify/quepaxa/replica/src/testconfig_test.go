package raxos

import "raxos/configuration"

// testConfig is a configuration of 3 replicas and one client (name 21) on loopback.
func testConfig() configuration.InstanceConfig {
	cfg := configuration.InstanceConfig{}
	for _, n := range []string{"1", "2", "3"} {
		cfg.Peers = append(cfg.Peers, configuration.ReplicaInstance{Name: n, IP: "127.0.0.1",
			PROXYPORT: "0", RECORDERPORT: "0"})
	}
	cfg.Clients = append(cfg.Clients, configuration.ClientInstance{Name: "21", IP: "127.0.0.1", CLIENTPORT: "0"})
	return cfg
}
