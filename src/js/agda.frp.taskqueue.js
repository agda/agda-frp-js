define(function() {
    // A task queue, containing tasks where
    // task.uid       -- a unique id for the task
    // task.rank      -- inside a time slice, tasks are executed in rank order
    // task.run(now)  -- the callback to execute the task
    function TaskQueue() {
	var self = this;
	this.futureTasks = {};      // Tasks to perform in the future, indexed by [time][uid]
	this.running = false;       // Are tasks currently being executed
	this.time = Date.now();     // The current time being executed
	this.rank = 0;              // The current rank being executed
	this.tasks = {};            // Tasks to run now, indexed by by [rank][uid]
	this.wakeupTime = Infinity; // When to wake up next
	this.wakeupHandle = null;   // The handle for the next wakeup call
	this.wakeupCallback =       // The callback for wakeups
          function() { self.run(Date.now()); };
    }
    TaskQueue.prototype.run = function(now) {
 	this.wakeupTime = Infinity;
	this.wakeupHandle = null;
	this.running = true;
	var taskTime = Math.min.apply(Math,Object.keys(this.futureTasks));
	while (taskTime <= now) {
	    var unranked = this.futureTasks[taskTime]
	    delete this.futureTasks[taskTime];
	    this.time = taskTime;
	    for (var uid in unranked) {
		var task = unranked[uid];
		if (!this.tasks[task.rank]) { this.tasks[task.rank] = {}; }
		this.tasks[task.rank][task.uid] = task;
	    }
	    var taskRank = Math.min.apply(Math,Object.keys(this.tasks));
	    while (taskRank < Infinity) {
		var running = this.tasks[taskRank];
		delete this.tasks[taskRank];
		this.rank = taskRank;
		for (var uid in running) {
		    running[uid].run(taskTime);
		}
		taskRank = Math.min.apply(Math,Object.keys(this.tasks));
	    }
	    taskTime = Math.min.apply(Math,Object.keys(this.futureTasks));
	}
	this.time = now;
	this.running = false;
	this.wakeup(taskTime);
    };
    TaskQueue.prototype.wakeup = function(when) {
	if ((!this.running) && (when < this.wakeupTime)) {
	    if (this.wakeupHandle) {
		clearTimeout(this.wakeupHandle);
	    }
	    this.wakeupTime = when;
	    this.wakeupHandle = setTimeout(this.wakeupCallback,when-Date.now());
	}
    };
    // A task can be scheduled if this.time <= when.
    // We ignore tasks which are being scheduled in the past.
    TaskQueue.prototype.schedule = function(when,task) {
	if (this.time === when) {
	    if (this.rank < task.rank) {
		if (!this.tasks[task.rank]) { this.tasks[task.rank] = {}; }
		this.tasks[task.rank][task.uid] = task;
		this.wakeup(when);
	    } else {
		task.run(when);
	    }
	} else if (this.time < when) {
	    if (!this.futureTasks[when]) { this.futureTasks[when] = {}; }
	    this.futureTasks[when][task.uid] = task;
	    this.wakeup(when);
	}
    };
    TaskQueue.prototype.reRank = function(oldRank,task) {
	if (this.tasks[oldRank] && this.tasks[oldRank][task.uid]) {
	    delete this.tasks[oldRank][task.uid];
	    if (!this.tasks[task.rank]) { this.tasks[task.rank] = {}; }
	    this.tasks[task.rank][task.uid] = task;
	}
    };
    return {
	singleton: new TaskQueue()
    };
})