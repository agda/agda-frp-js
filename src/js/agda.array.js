define(function() {
    function IArray(array,offset) {
	this.array = array;
	this.offset = offset;
    }
    IArray.prototype.head = function() { return this.array[this.offset]; }
    IArray.prototype.tail = function() { return new IArray(this.array,this.offset+1); }
    IArray.prototype.cons = function(x) {
	var offset = this.offset - 1;
	var array = this.array;
        if ((array[offset] !== undefined) && (array[offset] !== x)) {
	    array = array.slice(0);
	}
	array[offset] = x;
	return new IArray(array,offset);
    }
    return {
	iarray: function(array,offset) {
	    offset = offset || 0; 
	    return new IArray(array,offset);
	},
	iempty: function(offset) {
	    return new IArray(new Array(offset),offset);
	},
	equals: function(as,bs,p) {
	    p = p || function(a,b) { return a == b; };
	    if (as.length != bs.length) { return false; }
	    function q(a,i) { return p(a,bs[i]); }
	    return as.every(q);
	},
	subseteq: function(as,bs,p) {
	    p = p || function(a,b) { return a == b; };
	    if (as.length > bs.length) { return false; }
	    function q(a,i) { return p(a,bs[i]); }
	    return as.every(q);
	},
        lookup: function(as,i) {
	    return as[i];
	},
        singleton: function(a) {
	    return [a];
	},
	empty: []
    };
});