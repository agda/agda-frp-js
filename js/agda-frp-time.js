define(["./agda-frp-signal"],function(signal) { 
    function getTime(now) {
	return now;
    }
    function timeMod(delay) {
	var start = Date.now() + delay - 1;
	start = start - (start % delay);
	return signal.heartbeat(start,delay,0).map(getTime).hold(start);
    }
    return {
	seconds: function() { return timeMod(1000); },
	minutes: function() { return timeMod(60 * 1000); },
	hours: function() { return timeMod(60 * 60 * 1000); }
    };
});
