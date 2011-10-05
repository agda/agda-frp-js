define(["agda.frp.taskqueue","agda.mixin"],function(taskqueue,mixin) {
    // Signals are implemented as nodes in a dataflow graph.
    //
    // The lifecycle of a signal is:
    //
    // a) Signal creation at time s
    // b) Addition of new upstream neighbours at time s
    // c) Signal freezing at time s+1
    // d) Removal of upstream neighbours at time t (where s <= t)
    // d) Signal disposal at time t (where s < t)
    //
    // Signal disposal is automatically triggered when a signal has no
    // upstream neighbours, which removes itself from its downstream
    // neighbours.  (This is a workaround for ECMAScript not providing
    // weak references.)
    //
    // The abstract superclass of signals.
    // Each signal has a *rank*, such that
    // a) the rank of every signal is at least that of its downstream neighbours
    // b) the rank of a signal with more than one downstream neighour
    //    is strictly greer than that of its downstream neighbours.
    var signals = 0;
    function Signal() {
	this.uid = signals++;
	this.start = this.taskQueue.time;
	this.upstream = {};
	this.setRank();
	this.freezeLater();
    }
    mixin.singleton.mixin(Signal.prototype);
    Signal.prototype.taskQueue = taskqueue.singleton;
    Signal.prototype.addUpstream = function(signal) {
	if (this.taskQueue.time <= this.start) {
	    this.upstream[signal.uid] = signal;	    
	} else {
	    throw(new Error("Upstream neighbour added after start time."));
	}
    };
    Signal.prototype.removeUpstream = function(signal) {
	delete this.upstream[signal.uid];
	this.check();
    };
    Signal.prototype.notifyUpstream = function(now,value) {
	for (uid in this.upstream) {
	    this.upstream[uid].notify(now,value);
	}
    };
    // If the rank of a signal changes, we update the rank of its upstream neighbours
    Signal.prototype.rank = 0;
    Signal.prototype.setRank = function() {
	var rank = this.getRank();
	if (this.rank !== rank) {
	    var old = this.rank;
	    this.rank = rank;
	    this.taskQueue.reRank(old,this);
	    for (uid in this.upstream) {
		this.upstream[uid].setRank();
	    }
	}
    }
    // Check to see if a signal has no upstream neighbours (in which
    // case we can call dispose on it)
    Signal.prototype.check = function() {
	if (this.start < this.taskQueue.time) {
	    for (uid in this.upstream) { return; }
	    this.dispose();
	}
    }
    // Whenever a signal is built, we schedule a later call to signal.freeze.
    // By default, freeze disposes of a signal if it has no upstream neighbours.
    var freezer = {
	uid: 0,
	rank: 0,
	signals: [],
	add: function(signal) {
	    if (!signals.length) { signal.taskQueue.schedule(signal.start + 1, this); }
	    this.signals.push(signal);
	},
	run: function(now) {
	    while (this.signals.length) {
		this.signals.pop().freeze();
	    }
	}
    };
    Signal.prototype.freeze = Signal.prototype.check;
    Signal.prototype.freezeLater = function() { freezer.add(this); }
    // A signal with no downstream neighbours
    function Signal0() {
	Signal.call(this);
    }
    Signal.prototype.mixin(Signal0.prototype);
    Signal0.prototype.dispose = function() {};
    Signal0.prototype.getRank = function() { return 0; }
    // A signal with one downstream neighbour
    function Signal1(downstream) {
	this.downstream = downstream;
	Signal.call(this);
	downstream.addUpstream(this);
    }
    Signal.prototype.mixin(Signal1.prototype);
    Signal1.prototype.getRank = function() { 
	return this.downstream.rank;
    }
    Signal1.prototype.dispose = function() { 
	this.downstream.check();
    };
    // A signal with two downstream neighbours
    function Signal2(downstream1,downstream2) {
	this.downstream1 = downstream1;
	this.downstream2 = downstream2;
	Signal.call(this);
	downstream1.addUpstream(this);
	downstream2.addUpstream(this);
    }
    Signal.prototype.mixin(Signal2.prototype);
    Signal2.prototype.getRank = function() { 
	return 1 + Math.max(this.downstream1.rank,this.downstream2.rank);
    }
    Signal2.prototype.dispose = function() {
	this.downstream1.check();
	this.downstream2.check();
    };
    // A signal with an array of downstream neighbours
    function Signal$(downstream) {
	this.downstream = downstream;
	Signal.call(this);
	for (var i = 0 ; i < downstream.length ; i++) {
	    downstream[i].addUpstream(this);
	}
    }
    Signal.prototype.mixin(Signal$.prototype);
    Signal$.prototype.getRank = function() { 
	var result = 0;
	for (var i = 0 ; i < this.downstream.length ; i++) {
	    if (result <= this.downstream[i].rank) {
		result = this.downstream[i].rank + 1;
	    }
	}
	return result;
    }
    Signal$.prototype.dispose = function() {
	for (var i = 0 ; i < this.downstream.length ; i++) {
	    this.downstream[i].check();
	}
    };
    // Events are signals generating discrete signals.  During the
    // timeslice when an event is created, new upstream neighbours can
    // be added. This means that if an event arrives during the start
    // time, it must be cached, in order to forward it to any new
    // upstream neighbours. When the signal is frozen, we delete the cached
    // value (so that it doesn't get in the way of gc).
    function Event() {}
    mixin.singleton.mixin(Event.prototype);
    Event.prototype.addUpstream = function(signal) {
	Signal.prototype.addUpstream.call(this,signal);
	if (this.init !== undefined) { signal.notify(this.start,this.init); }
    }
    Event.prototype.notifyUpstream = function(now,value) {
	if (this.start === now) { this.init = value; }
	Signal.prototype.notifyUpstream.call(this,now,value);
    }
    Event.prototype.freeze = function() {
	delete this.init;
	Signal.prototype.freeze.call(this);
    }
    Event.prototype.map = function(fun) {
	return new MapEvent(fun,this);
    }
    Event.prototype.accumBy = function(fun,init) {
	return new AccumByEvent(fun,init,this);
    }
    Event.prototype.merge = function(event) {
	return new MergeEvent([this,event]);
    }
    Event.prototype.filter = function(pred) {
	return new FilterEvent(pred,this);
    }
    Event.prototype.delay = function(delay) {
	return new DelayEvent(delay,this);
    }
    Event.prototype.hold = function(init) {
	return new HoldBehaviour(init,this);
    }
    Event.prototype.switcher = function(init) {
	return new SwitchBehaviour(init,this);
    }
    // Events with zero, one, two or many downstream neighbours
    function Event0() {
	Signal0.call(this);
	Event.call(this);
    }
    Event.prototype.mixin(Signal0.prototype.mixin(Event0.prototype));
    function Event1(downstream) {
	Signal1.call(this,downstream);
	Event.call(this);
    }
    Event.prototype.mixin(Signal1.prototype.mixin(Event1.prototype));
    function Event2(downstream1,downstream2) {
	Signal2.call(this,downstream1,downstream2);
	Event.call(this);
    }
    Event.prototype.mixin(Signal2.prototype.mixin(Event2.prototype));
    function Event$(downstream) {
	Signal$.call(this,downstream);
	Event.call(this);
    }
    Event.prototype.mixin(Signal$.prototype.mixin(Event$.prototype));
    // An event which never fires
    function ZeroEvent() {
	Event0.call(this);
    }
    Event0.prototype.mixin(ZeroEvent.prototype);
    // An event which fires once
    function OneEvent(when,value) {
	this.value = value;
	this.when = when;
	Event0.call(this);
	this.taskQueue.schedule(when,this);
    }
    Event0.prototype.mixin(OneEvent.prototype);
    OneEvent.prototype.run = function(now) {
	this.notifyUpstream(now,this.value);
	delete this.value;
    }
    // Map a function onto a event
    function MapEvent(fun,downstream) {
	this.fun = fun;
	Event1.call(this,downstream);
    }
    Event1.prototype.mixin(MapEvent.prototype);
    MapEvent.prototype.notify = function(now,value) {
	this.notifyUpstream(now,this.fun(now,value));
    }
    // Accumulate a function over an event
    function AccumByEvent(fun,init,downstream) {
	this.fun = fun;
	this.state = init;
	Event1.call(this,downstream);
    }
    Event1.prototype.mixin(AccumByEvent.prototype);
    AccumByEvent.prototype.notify = function(now,value) {
	this.state = this.fun(now,this.state,value);
	this.notifyUpstream(now,this.state);
    }
    // Merge event streams
    function MergeEvent(downstream) {
	Event$.call(this,downstream);
    }
    Event$.prototype.mixin(MergeEvent.prototype);
    MergeEvent.prototype.notify = function(now,value) {
	this.value = value;
	this.taskQueue.schedule(now,this);
    }
    MergeEvent.prototype.run = function(now) {
	// This is a nondeterministic merge.
	this.notifyUpstream(now,this.value);
	delete this.value;
    }
    MergeEvent.prototype.merge = function(event) {
	var downstream;
	if (event.constructor === MergeEvent) {
	    downstream = this.downstream.concat(event.downstream);
	} else {
	    downstream = this.downstream.concat(event);
	}
	return new MergeEvent(downstream);
    }
    // Filter an event stream
    function FilterEvent(pred,downstream) {
	this.pred = pred;
	Event1.call(this,downstream);
    }
    Event1.prototype.mixin(FilterEvent.prototype);
    FilterEvent.prototype.notify = function(now,value) {
	if (this.pred(now,value)) {
	    this.notifyUpstream(now,value);
	}
    }
    // Delay an event stream
    function DelayEvent(delay,downstream) {
	this.delay = delay;
	this.buffer = {};
	Event1.call(this,downstream);
    }
    Event1.prototype.mixin(DelayEvent.prototype);
    DelayEvent.prototype.notify = function(now,value) {
	var later = now + this.delay;
	this.buffer[later] = value;
	this.taskQueue.schedule(later,this);
    }
    DelayEvent.prototype.getRank = function() {
	// Decoupled events get rank 0
	if (this.delay > 0) {
	    return 0;
	} else {
	    return downstream.rank;
	}
    }
    DelayEvent.prototype.run = function(now) {
	this.notifyUpstream(now,this.buffer[now]);
	delete this.buffer[now];
    }
    // A heartbeat event
    function HeartBeatEvent(when,delay,value) {
	this.delay = delay;
	this.value = value;
	this.run(when);
	Event0.call(this);
    }
    Event0.prototype.mixin(HeartBeatEvent.prototype);
    HeartBeatEvent.prototype.run = function(now) {
	this.taskQueue.schedule(now + this.delay,this);
	this.notifyUpstream(now,this.value);
    }
    HeartBeatEvent.prototype.dispose = function(now) {
	this.run = function(now) {};
    }
    // Convert a boolean behaviour into an event
    function EdgeEvent(downstream) {
	Event1.call(this,downstream);
    }
    Event1.prototype.mixin(EdgeEvent.prototype);
    EdgeEvent.prototype.notify = function(now,value) {
	if (value) {
	    this.notifyUpstream(now,true);
	}
    }
    // Behaviours are contiguous signals, which cache their most recent result
    function Behaviour() {}
    mixin.singleton.mixin(Behaviour.prototype);
    Behaviour.prototype.addUpstream = function(signal) {
	Signal.prototype.addUpstream.call(this,signal);
	signal.notify(this.start,this.value);
    }
    Behaviour.prototype.notifyUpstream = function(now,value) {
	if (this.value !== value) {
	    this.value = value;
	    Signal.prototype.notifyUpstream.call(this,now,value);
	}
    }
    Behaviour.prototype.map = function(fun) {
	return new MapBehaviour(fun,this);
    }
    Behaviour.prototype.text = function() {
	return new TextBehaviour(this);
    }
    Behaviour.prototype.attribute = function(key) {
	return new AttributeBehaviour(key,this);
    }
    Behaviour.prototype.concat = function(other) {
	return new ConcatBehaviour(this,other);
    }
    // Behaviours with zero, one, or two downstream neighbours
    function Behaviour0() {
	Signal0.call(this);
        Behaviour.call(this);
    }
    Behaviour.prototype.mixin(Signal0.prototype.mixin(Behaviour0.prototype));
    function Behaviour1(downstream) {
	Signal1.call(this,downstream);
        Behaviour.call(this);
    }
    Behaviour.prototype.mixin(Signal1.prototype.mixin(Behaviour1.prototype));
    function Behaviour2(downstream1,downstream2) {
	Signal2.call(this,downstream1,downstream2);
        Behaviour.call(this);
    }
    Behaviour.prototype.mixin(Signal2.prototype.mixin(Behaviour2.prototype));
    // A constant behaviour
    function ConstantBehaviour(value) {
	this.value = value;
	Behaviour0.call(this);
    }
    Behaviour0.prototype.mixin(ConstantBehaviour.prototype);
    // Map a function onto a event
    function MapBehaviour(fun,downstream) {
	this.fun = fun;
	Behaviour1.call(this,downstream);
    }
    Behaviour1.prototype.mixin(MapBehaviour.prototype);
    MapBehaviour.prototype.notify = function(now,value) {
	this.notifyUpstream(now,this.fun(now,value));
    }
    // Convert an event into a behaviour
    function HoldBehaviour(init,downstream) {
	this.value = init;
	Behaviour1.call(this,downstream);
    }
    Behaviour1.prototype.mixin(HoldBehaviour.prototype);
    HoldBehaviour.prototype.notify = function(now,value) {
	this.notifyUpstream(now,value);
    }
    // Convert an event of behaviours into a behaviour
    function SwitcherSignal(downstream) {
	Signal1.call(this,downstream);
    }
    Signal1.prototype.mixin(SwitcherSignal.prototype);
    SwitcherSignal.prototype.notify = function(now,signal) {
	for (uid in this.upstream) {
	    this.upstream[uid].switchTo(now,signal);
	}
    }
    function SwitchBehaviour(init,downstream) {
	Behaviour2.call(this,init,new SwitcherSignal(downstream));
    }
    Behaviour2.prototype.mixin(SwitchBehaviour.prototype);
    SwitchBehaviour.prototype.notify = function(now,value) {
	this.taskQueue.schedule(now,this);
    }
    SwitchBehaviour.prototype.switchTo = function(now,behaviour) {
	if (this.downstream1 !== behaviour) {
	    this.downstream1.removeUpstream(this);
	    this.downstream1 = behaviour;
	    this.setRank();
	    behaviour.addUpstream(this);
	}
    }
    SwitchBehaviour.prototype.run = function(now) {
	this.notifyUpstream(now,this.downstream1.value);
    }
    // DOMNodesBehaviour, Behaviour<DOMNodesBehaviour>
    function DOMNodesBehaviour() {
	this.value = this;
    }
    mixin.singleton.mixin(DOMNodesBehaviour.prototype);
    DOMNodesBehaviour.prototype.setChildrenOf = function(node) {
	this.replaceChildrenOf(node,0);
	while (node.childNodes.length > this.length) {
	    node.removeChild(node.lastChild);
	}
	if (node.attributes.length > this.attributes) {
	    var keys = [];
	    for (var i = 0; i < node.attributes.length; i++) {
		var key = node.attributes.index(x).name;
		if (!this.hasAttribute(key)) {
		    key.push(key);
		}
	    }
	    for (var i = 0; i < keys.length; i++) {
		node.removeAttribute(keys[i]);
	    }
	}
    }
    DOMNodesBehaviour.prototype.replaceChildrenOf = function(node,index) {
	if (node.childNodes.length > index) {
	    this.replaceChildrenAt(node,index);
	} else {
	    this.appendChildrenOf(node);
	}
    }
    DOMNodesBehaviour.prototype.attachTo = function(node) {
	// We add a dummy upstream neighbour to stop us from being disposed of
	this.addUpstream({ uid: -1, rank: this.rank, notify: function(){} });
	while (node.firstChild) { node.removeChild(node.firstChild); }
	this.appendChildrenOf(node);
    }
    DOMNodesBehaviour.prototype.addEventListener = function(type,listener) {}
    DOMNodesBehaviour.prototype.removeEventListener = function(type,listener) {}
    DOMNodesBehaviour.prototype.attributes = 0;
    DOMNodesBehaviour.prototype.hasAttribute = function(key) { return false; }
    // EmptyBehaviour <: DOMNodesBehaviour, Behaviour0<EmptyBehaviour>
    function EmptyBehaviour() {
	DOMNodesBehaviour.call(this);
	Behaviour0.call(this);
    }
    DOMNodesBehaviour.prototype.mixin(Behaviour0.prototype.mixin(EmptyBehaviour.prototype));
    EmptyBehaviour.prototype.appendChildrenOf = function(node) {}
    EmptyBehaviour.prototype.replaceChildrenAt = function(node,index) {}
    EmptyBehaviour.prototype.length = 0;
    // ConcatBehaviour <: DOMNodesBehaviour, Behaviour2<Behaviour<DOMNodesBehaviour>,Behaviour<DOMNodesBehaviour>,ConcatBehaviour>
    function ConcatBehaviour(downstream1,downstream2) {
	DOMNodesBehaviour.call(this);
	Behaviour2.call(this,downstream1,downstream2);
    }
    DOMNodesBehaviour.prototype.mixin(Behaviour2.prototype.mixin(ConcatBehaviour.prototype));
    ConcatBehaviour.prototype.notify = function(now,value) {
        this.length = this.downstream1.length + this.downstream2.length;
        this.attributes = this.downstream1.attributes + this.downstream2.attributes;
	this.notifyUpstream(now,this);
    }
    ConcatBehaviour.prototype.appendChildrenOf = function(node) {
	this.downstream1.value.appendChildrenOf(node);
	this.downstream2.value.appendChildrenOf(node);
    }
    ConcatBehaviour.prototype.replaceChildrenAt = function(node,index) {
	this.downstream1.value.replaceChildrenAt(node,index);
	this.downstream2.value.replaceChildrenOf(node,index+this.downstream.value.length);
    }
    ConcatBehaviour.prototype.addEventListener = function(type,listener) {
	this.downstream1.value.addEventListener(type,listener);
	this.downstream2.value.addEventListener(type,listener);
    }
    ConcatBehaviour.prototype.removeEventListener = function(type,listener) {
	this.downstream1.value.removeEventListener(type,listener);
	this.downstream2.value.removeEventListener(type,listener);
    }
    ConcatBehaviour.prototype.hasAttribute = function(key) {
	return this.downstream1.value.hasAttribute(key) || this.downstream2.value.hasAttribute(key);
    }
    // AttributeBehaviour <: DOMNodesBehaviour, Behaviour1<Behaviour<String>,AttributeBehaviour>
    function AttributeBehaviour(key,downstream) {
	this.key = key;
	this.pool = [];
	DOMNodesBehaviour.call(this);
	Behaviour1.call(this,downstream);
    }
    DOMNodesBehaviour.prototype.mixin(Behaviour1.prototype.mixin(AttributeBehaviour.prototype));
    AttributeBehaviour.prototype.notify = function(now,value) {
	for (var i = 0; i < this.pool.length; i++) {
	    this.pool[i].value = value;
	}
    }
    AttributeBehaviour.prototype.appendChildrenOf = function(node) {
	for (var i = 0; i < this.pool.length; i++) {
	    var owner = this.pool[i].ownerElment;
	    if ((!owner) || (owner === node )) {
		node.setAttributeNode(this.pool[i]);
		return;
	    }
	}
	var attr = document.createAttribute(this.key);
	this.pool.push(attr);
	attr.value = this.downstream.value;
	node.setAttributeNode(attr);
    }
    AttributeBehaviour.prototype.replaceChildrenAt = function(node,index) {
	this.appendChildrenOf(node);
    }
    AttributeBehaviour.prototype.attributes = 1;
    AttributeBehaviour.prototype.hasAttribute = function(key) {
	return this.key === key;
    }
    // DOMNodeBehaviour <: DOMNodesBehaviour, Behaviour<DOMNodeBehaviour>
    function DOMNodeBehaviour() {
	this.pool = [];
	DOMNodesBehaviour.call(this);
    }
    DOMNodesBehaviour.prototype.mixin(DOMNodeBehaviour.prototype);
    DOMNodeBehaviour.prototype.notify = function(now,value) {
	for (var i = 0; i < this.pool.length; i++) {
	    this.update(this.pool[i],value);
	}
    }
    DOMNodeBehaviour.prototype.appendChildrenOf = function(node) {
	for (var i = 0; i < this.pool.length; i++) {
	    if(!this.pool[i].parentNode) {
		node.appendChild(this.pool[i]);
		return;
	    }
	}
	var fresh = this.build();
	this.pool.push(fresh);
	node.appendChild(fresh);
    }
    DOMNodeBehaviour.prototype.replaceChildrenAt = function(node,index) {
	for (var i = 0; i < this.pool.length; i++) {
	    if((!this.pool[i].parentNode) || ((this.pool[i].parentNode === this) && (index <= this.pool[i].index))) {
		node.insertBefore(node.childNodes[index],this.pool[i]);
		return;
	    }
	}
	var fresh = this.build();
	this.pool.push(fresh);
	node.insertBefore(node.childNodes[i],fresh);
    }
    DOMNodeBehaviour.prototype.length = 1;
    // TextBehaviour <: DOMNodeBehaviour, Behaviour1<String,TextBehaviour>
    function TextBehaviour(downstream) {
	DOMNodeBehaviour.call(this);
	Behaviour1.call(this,downstream);
    }
    DOMNodeBehaviour.prototype.mixin(Behaviour1.prototype.mixin(TextBehaviour.prototype));
    TextBehaviour.prototype.update = function(node,value) {
	node.replaceData(0,node.length,value);
    }
    TextBehaviour.prototype.build = function() {
	return document.createTextNode(this.downstream.value);
    }
    // ElementBehaviour <: DOMNodeBehaviour, Behaviour2<Behaviour<DOMNodesBehaviour>,DOW,ElementBehaviour>
    function ElementBehaviour(tag,downstream1,downstream2) {
	this.tag = tag;
	DOMNodeBehaviour.call(this);
	Behaviour2.call(this,downstream1,downstream2);
    }
    DOMNodeBehaviour.prototype.mixin(Behaviour2.prototype.mixin(ElementBehaviour.prototype));
    ElementBehaviour.prototype.update = function(node,value) {
	value.setChildrenOf(node);
    }
    ElementBehaviour.prototype.build = function() {
	var result = document.createElement(this.tag);
	this.downstream1.value.appendChildrenOf(result);
	this.downstream2.addEventListenersTo(result);
	return result;
    }
    ElementBehaviour.prototype.addEventListener = function(type,listener) {
	for (var i = 0; i < this.pool.length; i++) {
	    this.pool[i].addEventListener(type,listener);
	}
    }
    ElementBehaviour.prototype.removeEventListener = function(type,listener) {
	for (var i = 0; i < this.pool.length; i++) {
	    this.pool[i].removeEventListener(type,listener);
	}
    }
    // Document Object World, provides context (in particular event streams) for DOM behaviours
    function DOW() {
    }
    DOW.prototype.rank = 0;
    DOW.prototype.child = function(tag) {
	if (!this.children) { 
	    this.children = {};
	}
	var result = this.children[tag];
	if (!result) {
	    result = new DOW();
	    this.children[tag] = result;
	}
	return result;
    };
    DOW.prototype.left = function() {
	return this.child(0);
    };
    DOW.prototype.right = function() {
	return this.child(1);
    };
    DOW.prototype.element = function(a,b) {
	return new ElementBehaviour(a,b,this);
    };
    DOW.prototype.addEventListenersTo = function(node) {
	if (this.upstreamE) { for (uid in this.upstreamE) {
	    node.addEventListener(this.upstreamE[uid].eventType,this.upstreamE[uid]);
	} }
    }	
    DOW.prototype.addUpstream = function(upstream) {
	// DOW nodes have two types of upstream neighbours:
	// DOMNodeBehaviours and DOWEvents.  As a hack, we distinguish
	// between them based on the existence of upstream.eventType
	if (upstream.eventType) {
	    if (!this.upstreamE) { this.upstreamE = {}; }
	    this.upstreamE[upstream.uid] = upstream;
	    for (uid in this.upstreamB) {
		this.upstreamB[uid].addEventListener(upstream.eventType.upstream);
	    }
	} else {
	    if (!this.upstreamB) { this.upstreamB = {}; }
	    this.upstreamB[upstream.uid] = upstream;
	    for (uid in this.upstreamE) {
		upstream.addEventListener(this.upstreamE[uid].eventType,this.upstreamE[uid]);
	    }
	}
    };
    DOW.prototype.removeUpstream = function(upstream) {
	if (upstream.eventType) {
	    delete this.upstreamE[upstream.uid];
	    for (uid in this.upstreamB) {
		this.upstreamB[uid].removeEventListener(upstream.eventType.upstream);
	    }
	} else {
	    delete this.upstreamB[upstream.uid];
	    for (uid in this.upstreamE) {
		upstream.removeEventListener(this.upstreamE[uid].eventType,this.upstreamE[uid]);
	    }
	}
    }
    DOW.prototype.check = function() {};
    DOW.prototype.events = function(eventType) {
	return new DOWEvent(eventType,this);
    }; 
    // A DOW event stream
    var currentDOW = undefined;
    var currentDOWEvent = undefined;
    function DOWEvent(eventType,downstream) {
	var self = this;
	this.handleEvent = function(evt) {
	    // Low-level events must arrive at distinct times.
	    // This means we may get clock drift if events arrive
	    // at > 1000/s, hopefully that won't happen too often.
	    // Note that this means that bubbling DOM events will be
	    // considered as distinct FRP events.
	    // An alternative design would be to allow simultaneous
	    // low-level events, but this would require calling
	    // taskQueue.wakeup(now) rather than taskQueue.run(now)
	    // below, that is we'd have to schedule a later callback
	    // to process the task queue, rather than processing
	    // the queue right away. This is a trade-off between
	    // a cleaner semantics andf efficiency, caused by JS
	    // not having a callback which is triggered after event bubbling.
	    var now = Math.max(evt.timeStamp,self.taskQueue.time + 1);
	    currentDOW = self.downstream;
	    currentDOWEvent = evt;
	    self.event = evt;
	    self.taskQueue.scheduleRun(now,self);
	    self.event = undefined;
	    currentDOW = undefined;
	    currentDOWEvent = undefined;
	}
	this.eventType = eventType;
	Event1.call(this,downstream);
	if ((currentDOW === downstream) && (currentDOWEvent.type === eventType)) {
	    this.notifyUpstream(now,currentDOWEvent);
	}
    }
    Event1.prototype.mixin(DOWEvent.prototype);
    DOWEvent.prototype.run = function(now) {
	this.notifyUpstream(now,this.event);
    }
    // Geolocation, using the HTML5 geolocation API
    function GeolocationBehaviour() {
	var self = this;
	this.value = null;
	this.watcher = undefined;
	this.success = function(position) { 
	    self.notify(position.timestamp,position.coords);
	}
	this.error = function() { 
	    self.notify(self.taskQueue.now(),null);
	}
	Behaviour0.call(this);
    }
    Behaviour0.prototype.mixin(GeolocationBehaviour.prototype);
    GeolocationBehaviour.prototype.addUpstream = function(signal) {
	this.upstream[signal.uid] = signal;
	signal.notify(this.taskQueue.time,this.value);
	if (!this.watcher) {
	    this.watcher = navigator.geolocation.watchPosition(this.success,this.error);
	}
    }
    GeolocationBehaviour.prototype.dispose = function() {
	if (this.watcher) {
	    navigator.geolocation.clearWatch(this.watcher);
	    this.watcher = undefined;
	}
    }
    GeolocationBehaviour.prototype.notify = function(now,value) {
	// Low-level events must have distinct timestamps
	now = Math.max(now,this.taskQueue.time + 1);
	this.location = value;
	this.taskQueue.scheduleRun(now,this);
    }
    GeolocationBehaviour.prototype.run = function(now) {
	this.notifyUpstream(now,this.location);
    }
    var geolocation = new GeolocationBehaviour();
    // Exports
    return {
	zero: function() { return new ZeroEvent(); },
	one: function(when,value) { return new OneEvent(when,value); },
	heartbeat: function(when,delay,value) { return new HeartBeatEvent(when,delay,value); },
	constant: function(value) { return new ConstantBehaviour(value); },
        empty: function() { return new EmptyBehaviour(); },
	geolocation: function() { return geolocation; },
	reactimate: function(f) { return f(new DOW())(taskqueue.singleton.time); }
    };
});