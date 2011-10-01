define(function() {
    function IArray(array,offset) {
	this.array = array;
	this.offset = offset;
    }
    IArray.prototype.head = function() { return this.array[this.offset]; }
    IArray.prototype.tail = function() { return new IArray(this.array,this.offset+1); }
    IArray.prototype.lookup = function(i) { return this.array[i]; }
    IArray.prototype.cons = function(x) {
	var offset = this.offset - 1;
	var array;
        if (this.array[offset] === undefined) {
	    array = this.array;
	} else {
	    array = this.array.slice(0);
	}
	array[offset] = x;
	return new IArray(array,offset);
    }
    IArray.prototype.map = function(f,x) {
	var g;
	if (this.offset <= 0) {
	    g = f;
	} else {
	    g = function(a,i,as) { if (a !== undefined) { return f.call(this,a,i,as); } };
	}
	return new IArray(this.array.map(g,x),this.offset);
    }
    IArray.prototype.every = function(f,x) {
	var g;
	if (this.offset <= 0) {
	    g = f;
	} else if (x) {
	    g = function(a,i,as) { return (a === undefined) || f.call(this,a,i,as); };
	}
	this.array.every(g,x);
    }
    return {
	iarray: function(array) { return new IArray(array,0); },
	iempty: function(offset) { return new IArray(new Array(offset),offset); },
	ievery2: function(as,bs,f,x) {
	    if (as.array.length != bs.array.length) { return false; }
	    function g(a,i,as) { return (a === undefined) || f.call(this,a,bs[i],as,bs); }
	    return as.array.every(g,x);
	},
	every2: function(as,bs,f,x) {
	    if (as.length != bs.length) { return false; }
	    function g(a,i,as) { return f.call(this,a,bs[i],as,bs); }
	    return as.every(g,x);
	},
        lookup: function(as,i) { return as[i]; },
	empty: []
    };
});