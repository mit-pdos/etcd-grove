package apimodel

import (
	"context"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/util/intstr"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/client-go/kubernetes"
	appsv1client "k8s.io/client-go/kubernetes/typed/apps/v1"
	corev1client "k8s.io/client-go/kubernetes/typed/core/v1"
)

// Clientset is the model's kubernetes.Interface. Only CoreV1 and AppsV1 are implemented; the
// embedded interface is nil, so any other method panics.
type Clientset struct {
	kubernetes.Interface
	s     *Server
	admin bool
}

// Clientset returns a client of the server that sees the configured failures (the
// controller's).
func (s *Server) Clientset() *Clientset {
	return &Clientset{s: s}
}

// AdminClientset returns a client of the server that never sees a failure (the test
// program's).
func (s *Server) AdminClientset() *Clientset {
	return &Clientset{s: s, admin: true}
}

func (c *Clientset) CoreV1() corev1client.CoreV1Interface {
	return &coreV1{s: c.s, admin: c.admin}
}

func (c *Clientset) AppsV1() appsv1client.AppsV1Interface {
	return &appsV1{s: c.s, admin: c.admin}
}

type coreV1 struct {
	corev1client.CoreV1Interface
	s     *Server
	admin bool
}

func (c *coreV1) Pods(namespace string) corev1client.PodInterface {
	return &podClient{s: c.s, ns: namespace, admin: c.admin}
}

func (c *coreV1) Nodes() corev1client.NodeInterface {
	return &nodeClient{s: c.s, admin: c.admin}
}

func (c *coreV1) Events(namespace string) corev1client.EventInterface {
	return &eventClient{}
}

type appsV1 struct {
	appsv1client.AppsV1Interface
	s     *Server
	admin bool
}

func (c *appsV1) DaemonSets(namespace string) appsv1client.DaemonSetInterface {
	return &daemonSetClient{s: c.s, ns: namespace, admin: c.admin}
}

func (c *appsV1) ControllerRevisions(namespace string) appsv1client.ControllerRevisionInterface {
	return &revisionClient{s: c.s, ns: namespace, admin: c.admin}
}

// ---------------------------------------------------------------------------------------------
// Pods

func emptyPod() object { return &corev1.Pod{} }

// preparePod is pod's create strategy and the defaults the model applies.
func preparePod(o object) {
	pod := o.(*corev1.Pod)
	pod.Generation = 1
	pod.Status = corev1.PodStatus{Phase: corev1.PodPending}
	if pod.Spec.TerminationGracePeriodSeconds == nil {
		grace := int64(corev1.DefaultTerminationGracePeriodSeconds)
		pod.Spec.TerminationGracePeriodSeconds = &grace
	}
	if pod.Spec.RestartPolicy == "" {
		pod.Spec.RestartPolicy = corev1.RestartPolicyAlways
	}
	if pod.Spec.DNSPolicy == "" {
		pod.Spec.DNSPolicy = corev1.DNSClusterFirst
	}
	if pod.Spec.SchedulerName == "" {
		pod.Spec.SchedulerName = corev1.DefaultSchedulerName
	}
}

// podGrace is pod's CheckGracefulDelete: the grace period, 0 for an unbound or finished pod.
func podGrace(o object, opts metav1.DeleteOptions) int64 {
	pod := o.(*corev1.Pod)
	var period int64
	if opts.GracePeriodSeconds != nil {
		period = *opts.GracePeriodSeconds
	} else if pod.Spec.TerminationGracePeriodSeconds != nil {
		period = *pod.Spec.TerminationGracePeriodSeconds
	}
	if pod.Spec.NodeName == "" || pod.Status.Phase == corev1.PodFailed || pod.Status.Phase == corev1.PodSucceeded {
		period = 0
	}
	if period < 0 {
		period = 1
	}
	return period
}

type podClient struct {
	corev1client.PodInterface
	s     *Server
	ns    string
	admin bool
}

func (c *podClient) Create(ctx context.Context, pod *corev1.Pod, opts metav1.CreateOptions) (*corev1.Pod, error) {
	o, err := c.s.create(c.s.pods, c.ns, pod, preparePod, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*corev1.Pod), nil
}

func (c *podClient) Get(ctx context.Context, name string, opts metav1.GetOptions) (*corev1.Pod, error) {
	o, err := c.s.get(c.s.pods, c.ns, name, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*corev1.Pod), nil
}

func (c *podClient) List(ctx context.Context, opts metav1.ListOptions) (*corev1.PodList, error) {
	objs, rv, err := c.s.list(c.s.pods, c.ns, opts, c.admin)
	if err != nil {
		return nil, err
	}
	l := &corev1.PodList{ListMeta: metav1.ListMeta{ResourceVersion: rv}, Items: make([]corev1.Pod, len(objs))}
	for i, o := range objs {
		l.Items[i] = *o.(*corev1.Pod)
	}
	return l, nil
}

func (c *podClient) Watch(ctx context.Context, opts metav1.ListOptions) (watch.Interface, error) {
	return c.s.watch(c.s.pods, c.ns, opts, c.admin)
}

func (c *podClient) Delete(ctx context.Context, name string, opts metav1.DeleteOptions) error {
	return c.s.remove(c.s.pods, c.ns, name, opts, podGrace, c.admin)
}

// ---------------------------------------------------------------------------------------------
// Nodes

func emptyNode() object { return &corev1.Node{} }

func prepareNode(o object) {}

type nodeClient struct {
	corev1client.NodeInterface
	s     *Server
	admin bool
}

func (c *nodeClient) Create(ctx context.Context, node *corev1.Node, opts metav1.CreateOptions) (*corev1.Node, error) {
	o, err := c.s.create(c.s.nodes, "", node, prepareNode, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*corev1.Node), nil
}

func (c *nodeClient) Get(ctx context.Context, name string, opts metav1.GetOptions) (*corev1.Node, error) {
	o, err := c.s.get(c.s.nodes, "", name, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*corev1.Node), nil
}

func (c *nodeClient) List(ctx context.Context, opts metav1.ListOptions) (*corev1.NodeList, error) {
	objs, rv, err := c.s.list(c.s.nodes, "", opts, c.admin)
	if err != nil {
		return nil, err
	}
	l := &corev1.NodeList{ListMeta: metav1.ListMeta{ResourceVersion: rv}, Items: make([]corev1.Node, len(objs))}
	for i, o := range objs {
		l.Items[i] = *o.(*corev1.Node)
	}
	return l, nil
}

func (c *nodeClient) Watch(ctx context.Context, opts metav1.ListOptions) (watch.Interface, error) {
	return c.s.watch(c.s.nodes, "", opts, c.admin)
}

// ---------------------------------------------------------------------------------------------
// DaemonSets

func emptyDaemonSet() object { return &appsv1.DaemonSet{} }

// prepareDaemonSet is SetDefaults_DaemonSet and the DaemonSet create strategy.
func prepareDaemonSet(o object) {
	ds := o.(*appsv1.DaemonSet)
	strategy := &ds.Spec.UpdateStrategy
	if strategy.Type == "" {
		strategy.Type = appsv1.RollingUpdateDaemonSetStrategyType
	}
	if strategy.Type == appsv1.RollingUpdateDaemonSetStrategyType {
		if strategy.RollingUpdate == nil {
			strategy.RollingUpdate = &appsv1.RollingUpdateDaemonSet{}
		}
		if strategy.RollingUpdate.MaxUnavailable == nil {
			maxUnavailable := intstr.FromInt32(1)
			strategy.RollingUpdate.MaxUnavailable = &maxUnavailable
		}
		if strategy.RollingUpdate.MaxSurge == nil {
			maxSurge := intstr.FromInt32(0)
			strategy.RollingUpdate.MaxSurge = &maxSurge
		}
	}
	if ds.Spec.RevisionHistoryLimit == nil {
		limit := int32(10)
		ds.Spec.RevisionHistoryLimit = &limit
	}
	ds.Status = appsv1.DaemonSetStatus{}
	ds.Generation = 1
	if ds.Annotations == nil {
		ds.Annotations = make(map[string]string)
	}
	if ds.Annotations[appsv1.DeprecatedTemplateGeneration] == "" {
		ds.Annotations[appsv1.DeprecatedTemplateGeneration] = "1"
	}
}

// updateDaemonSetStatus is the status strategy: the stored object with the request's status,
// or nil when the status does not change.
func updateDaemonSetStatus(old object, req object) object {
	stored := old.(*appsv1.DaemonSet)
	status := req.(*appsv1.DaemonSet).Status
	if daemonSetStatusEqual(&stored.Status, &status) {
		return nil
	}
	stored.Status = status
	return stored
}

func int32PtrEqual(a *int32, b *int32) bool {
	if a == nil || b == nil {
		return a == nil && b == nil
	}
	return *a == *b
}

func daemonSetStatusEqual(a *appsv1.DaemonSetStatus, b *appsv1.DaemonSetStatus) bool {
	if a.CurrentNumberScheduled != b.CurrentNumberScheduled ||
		a.NumberMisscheduled != b.NumberMisscheduled ||
		a.DesiredNumberScheduled != b.DesiredNumberScheduled ||
		a.NumberReady != b.NumberReady ||
		a.ObservedGeneration != b.ObservedGeneration ||
		a.UpdatedNumberScheduled != b.UpdatedNumberScheduled ||
		a.NumberAvailable != b.NumberAvailable ||
		a.NumberUnavailable != b.NumberUnavailable ||
		!int32PtrEqual(a.CollisionCount, b.CollisionCount) ||
		len(a.Conditions) != len(b.Conditions) {
		return false
	}
	for i := range a.Conditions {
		x := a.Conditions[i]
		y := b.Conditions[i]
		if x.Type != y.Type || x.Status != y.Status || !x.LastTransitionTime.Equal(&y.LastTransitionTime) ||
			x.Reason != y.Reason || x.Message != y.Message {
			return false
		}
	}
	return true
}

type daemonSetClient struct {
	appsv1client.DaemonSetInterface
	s     *Server
	ns    string
	admin bool
}

func (c *daemonSetClient) Create(ctx context.Context, ds *appsv1.DaemonSet, opts metav1.CreateOptions) (*appsv1.DaemonSet, error) {
	o, err := c.s.create(c.s.daemonSets, c.ns, ds, prepareDaemonSet, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*appsv1.DaemonSet), nil
}

func (c *daemonSetClient) Get(ctx context.Context, name string, opts metav1.GetOptions) (*appsv1.DaemonSet, error) {
	o, err := c.s.get(c.s.daemonSets, c.ns, name, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*appsv1.DaemonSet), nil
}

func (c *daemonSetClient) List(ctx context.Context, opts metav1.ListOptions) (*appsv1.DaemonSetList, error) {
	objs, rv, err := c.s.list(c.s.daemonSets, c.ns, opts, c.admin)
	if err != nil {
		return nil, err
	}
	l := &appsv1.DaemonSetList{ListMeta: metav1.ListMeta{ResourceVersion: rv}, Items: make([]appsv1.DaemonSet, len(objs))}
	for i, o := range objs {
		l.Items[i] = *o.(*appsv1.DaemonSet)
	}
	return l, nil
}

func (c *daemonSetClient) Watch(ctx context.Context, opts metav1.ListOptions) (watch.Interface, error) {
	return c.s.watch(c.s.daemonSets, c.ns, opts, c.admin)
}

func (c *daemonSetClient) UpdateStatus(ctx context.Context, ds *appsv1.DaemonSet, opts metav1.UpdateOptions) (*appsv1.DaemonSet, error) {
	o, err := c.s.update(c.s.daemonSets, c.ns, ds, updateDaemonSetStatus, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*appsv1.DaemonSet), nil
}

// ---------------------------------------------------------------------------------------------
// ControllerRevisions

func emptyRevision() object { return &appsv1.ControllerRevision{} }

func prepareRevision(o object) {}

// replaceRevision is Update's mutation: the request's object, under the stored identity.
func replaceRevision(old object, req object) object {
	return req
}

type revisionClient struct {
	appsv1client.ControllerRevisionInterface
	s     *Server
	ns    string
	admin bool
}

func (c *revisionClient) Create(ctx context.Context, cr *appsv1.ControllerRevision, opts metav1.CreateOptions) (*appsv1.ControllerRevision, error) {
	o, err := c.s.create(c.s.revisions, c.ns, cr, prepareRevision, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*appsv1.ControllerRevision), nil
}

func (c *revisionClient) Get(ctx context.Context, name string, opts metav1.GetOptions) (*appsv1.ControllerRevision, error) {
	o, err := c.s.get(c.s.revisions, c.ns, name, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*appsv1.ControllerRevision), nil
}

func (c *revisionClient) List(ctx context.Context, opts metav1.ListOptions) (*appsv1.ControllerRevisionList, error) {
	objs, rv, err := c.s.list(c.s.revisions, c.ns, opts, c.admin)
	if err != nil {
		return nil, err
	}
	l := &appsv1.ControllerRevisionList{ListMeta: metav1.ListMeta{ResourceVersion: rv}, Items: make([]appsv1.ControllerRevision, len(objs))}
	for i, o := range objs {
		l.Items[i] = *o.(*appsv1.ControllerRevision)
	}
	return l, nil
}

func (c *revisionClient) Watch(ctx context.Context, opts metav1.ListOptions) (watch.Interface, error) {
	return c.s.watch(c.s.revisions, c.ns, opts, c.admin)
}

func (c *revisionClient) Update(ctx context.Context, cr *appsv1.ControllerRevision, opts metav1.UpdateOptions) (*appsv1.ControllerRevision, error) {
	o, err := c.s.update(c.s.revisions, c.ns, cr, replaceRevision, c.admin)
	if err != nil {
		return nil, err
	}
	return o.(*appsv1.ControllerRevision), nil
}

func (c *revisionClient) Delete(ctx context.Context, name string, opts metav1.DeleteOptions) error {
	return c.s.remove(c.s.revisions, c.ns, name, opts, noGrace, c.admin)
}

// ---------------------------------------------------------------------------------------------
// Events: accepted and dropped

type eventClient struct {
	corev1client.EventInterface
}

func (c *eventClient) CreateWithEventNamespace(event *corev1.Event) (*corev1.Event, error) {
	return event, nil
}

func (c *eventClient) UpdateWithEventNamespace(event *corev1.Event) (*corev1.Event, error) {
	return event, nil
}

func (c *eventClient) PatchWithEventNamespace(event *corev1.Event, data []byte) (*corev1.Event, error) {
	return event, nil
}

func (c *eventClient) CreateWithEventNamespaceWithContext(ctx context.Context, event *corev1.Event) (*corev1.Event, error) {
	return event, nil
}

func (c *eventClient) UpdateWithEventNamespaceWithContext(ctx context.Context, event *corev1.Event) (*corev1.Event, error) {
	return event, nil
}

func (c *eventClient) PatchWithEventNamespaceWithContext(ctx context.Context, event *corev1.Event, data []byte) (*corev1.Event, error) {
	return event, nil
}
