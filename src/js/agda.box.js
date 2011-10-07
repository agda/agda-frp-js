define (function() {
    function Box(level,prev) {
	this.level = level;
	this.prev = prev;
    }
    var boxes = [ new Box(0,null) ];
    function box(value) {
	if (value === undefined) {
	    return null;
	} else if (value === null) { 
	    return boxes[0];
	} else if (value.constructor === Box) {
	    var level = value.level + 1;
	    var box = boxes[level]
	    if (!box) {
		box = new Box(level,value);
		boxes[level] = box;
	    }
	    return box;
	} else {
	    return value;
	    }
    }
    function unbox(value) {
	if (value.constructor === Box) {
	    return value.prev;
	} else {
	    return value;
	}
    };
    function handle(fun) {
	return function(arg) {
	    try {
		return box(fun(arg));
	    } catch(e) {
		return null;
	    }
	};
    }
    return { box: box, unbox: unbox, handle: handle };
});