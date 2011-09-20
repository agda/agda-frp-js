define(["agda.frp.taskqueue","agda.frp.signal"],function(queue,signal) { 
    function getTime(now) {
	return now;
    }
    function every(delay) {
	var start = queue.singleton.time + delay - 1;
	start = start - (start % delay);
	return signal.heartbeat(start,delay,0).map(getTime).hold(start);
    }
    return {
	date: function(t) { return new Date(t); },
	seconds: function() { return every(1000); },
	minutes: function() { return every(60 * 1000); },
	hours: function() { return every(60 * 60 * 1000); },
	every: every
    };
});
