define(["agda.keys"],function(keys) {
    var keysOf;
    if (Object.keys) {
	keysOf = function(obj) {
	    return Object.keys(obj).sort();
	}
    } else {
	keysOf = function(obj) {
	    var result = [];
	    for (key in obj) {
		result.push(key);
	    }
	    return result.sort();
	}
    }
    var numKeys;
    if (Object.keys){
	numKeys = function(obj) {
	    return Object.keys(obj).length;
	}
    } else {
	numKeys = function(obj) {
	    var result = 0;
	    for (key in obj) {
		result++;
	    }
	    return result;
	}
    }
    var IKeys = keys.IKeys;
    function IObject(obj,array,offset) {
	this.obj = obj;
	IKeys.call(this,array,offset);
    }
    IKeys.prototype.mixin(IObject.prototype);
    IObject.prototype.key = function() {
	return this.array[this.offset];
    }
    IObject.prototype.value = function() {
	return this.obj[this.array[this.offset]];
    }
    IObject.prototype.tail = function() {
	return new IObject(this.obj,this.array,this.offset+1);
    }
    IObject.prototype.set = function(key,value) {
	var obj = this.obj;
	var keys = this.cons(key);
	var array = keys.array;
	var offset = keys.offset;
	if ((obj[key] !== undefined) && (obj[key] !== value)) {
	    var noo = {};
	    for (var i = offset; i < keys.length; i++) {
		noo[keys[i]] = obj[keys[i]];
	    }
	    obj = noo;
	}
	obj[key] = value;
	return new IObject(obj,array,offset);
    }
    IObject.prototype.object = function() {
	var obj = this.obj;
	var array = this.array;
	var offset = this.offset;
	if (numKeys(obj) == array.length - offset) {
	    return obj;
	} else {
	    var noo = {};
	    for (var i = offset; i < array.length; i++) {
		var key = array[i];
		noo[key] = obj[key];
	    }
	    this.obj = noo;
	    this.array = keysOf(noo);
	    this.offset = 0;
	    return noo;
	}
    }
    return {
	keys: keysOf,
	map: function(fun,obj) {
	    var noo = {};
	    for (var key in obj) {
		noo[key] = fun(obj[key],key);
	    }
	    return noo;
	},
	all: function(fun,obj) {
	    for (var key in obj) {
		if (!fun(obj[key],key)) { return false; }
	    }
	    return true;
	},
	filter: function(fun,obj) {
	    var noo = {};
	    for (var key in obj) {
		if (fun(obj[key],key)) { noo[key] = obj[key]; }
	    }
	    return noo;
	},
	iobject: function(obj) { return new IObject(obj,keysOf(obj),0); },
	lookup: function(obj,key) { return obj[key]; },
        iempty: function () { return new IObject({},[],0); },
        singleton: function(key,value) { var result = {}; result[key] = value; return result; }
    }
});