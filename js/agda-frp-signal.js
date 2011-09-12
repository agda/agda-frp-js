define(["./agda-frp-taskqueue","./agda-frp-mixin"],function(taskqueue,mixin) {
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
    Event.prototype.merge = function(event) {
	return new MergeEvent(this,event);
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
    // Events with zero, one, or two downstream neighbours
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
    // Merge two event streams
    function MergeEvent(downstream1,downstream2) {
	Event2.call(this,downstream1,downstream2);
    }
    Event2.prototype.mixin(MergeEvent.prototype);
    MergeEvent.prototype.notify = function(now,value) {
	this.value = value;
	this.taskQueue.schedule(now,this);
    }
    MergeEvent.prototype.run = function(now) {
	// This is a nondeterministic merge.
	this.notifyUpstream(now,value);
	delete this.value;
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
    // Convert a DOM node into an event
    var currentDOMEvent = undefined;
    function DOMEvent(dom,type) {
	var self = this;
	this.handler = function(evt) {
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
	    // the queue right away.  This is a trade-off between
	    // a cleaner semantics andf efficiency, caused by JS
	    // not having a callback which is triggered after event bubbling.
	    var now = Math.max(Date.now(),self.taskQueue.time + 1);
	    currentDOMEvent = evt;
	    self.notifyUpstream(now,evt);
	    self.taskQueue.run(now);
	    currentDOMEvent = undefined;
	}
	this.type = type;
	this.dom = dom;
	Event0.call(this);
	this.dom.addEventListener(this.type,this.handler);
	if (currentDOMEvent && (currentDOMEvent.currentTarget === dom) && (currentDOMEvent.type === type)) {
	    this.notifyUpstream(now,currentDOMEvent);
	}
    }
    Event0.prototype.mixin(DOMEvent.prototype);
    DOMEvent.prototype.dispose = function() {
	this.dom.removeEventListener(this.type,this.handler);
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
    Behaviour.prototype.element = function(tag) {
	return new ElementBehaviour(tag,this);
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
	while (node.children.length > this.length) {
	    node.removeChild(node.lastChild);
	}
    }
    DOMNodesBehaviour.prototype.replaceChildrenOf = function(node,index) {
	if (node.children.length > index) {
	    this.replaceChildrenAt(node,index);
	} else {
	    this.appendChildrenOf(node);
	}
    }
    DOMNodesBehaviour.prototype.attachTo = function(node) {
	// We add a dummy upstream neighbour to stop us from being disposed of
	this.addUpstream({ uid: -1, rank: this.rank, notify: function(){} });
	this.appendChildrenOf(node);
    }
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
		node.insertBefore(node.children[index],this.pool[i]);
		return;
	    }
	}
	var fresh = this.build();
	this.pool.push(fresh);
	node.insertBefore(node.children[i],fresh);
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
    // AttributeBehaviour <: DOMNodeBehaviour, Behaviour1<Behaviour<String>,AttributeBehaviour>
    function AttributeBehaviour(key,downstream) {
	this.key = key;
	DOMNodeBehaviour.call(this);
	Behaviour1.call(this,downstream);
    }
    DOMNodeBehaviour.prototype.mixin(Behaviour1.prototype.mixin(AttributeBehaviour.prototype));
    AttributeBehaviour.prototype.update = function(node,value) {
	node.setValue(value);
    }
    AttributeBehaviour.prototype.build = function() {
	return document.createAttributeNode(this.key,this.downstream.value);
    }
    // ElementBehaviour <: DOMNodeBehaviour, Behaviour1<Behaviour<DOMNodesBehaviour>,ElementBehaviour>
    function ElementBehaviour(tag,downstream) {
	this.tag = tag;
	DOMNodeBehaviour.call(this);
	Behaviour1.call(this,downstream);
    }
    DOMNodeBehaviour.prototype.mixin(Behaviour1.prototype.mixin(ElementBehaviour.prototype));
    ElementBehaviour.prototype.update = function(node,value) {
	value.setChildrenOf(node);
    }
    ElementBehaviour.prototype.build = function() {
	var result = document.createElement(this.tag);
	this.downstream.value.appendChildrenOf(result);
	return result;
    }
    // Exports
    return {
	zero: function() { return new ZeroEvent(); },
	one: function(when,value) { return new OneEvent(when,value); },
	heartbeat: function(when,delay,value) { return new HeartBeatEvent(when,delay,value); },
	constant: function(value) { return new ConstantBehaviour(value); },
        empty: function() { return new EmptyBehaviour(); }
    };
});