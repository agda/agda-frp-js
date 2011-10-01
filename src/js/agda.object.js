define(["agda.keys"],function(keys) {
    var keysOf;
    if (Object.keys) {
	keysOf = function(object) {
	    return Object.keys(object).sort();
	}
    } else {
	keysOf = function(object) {
	    var result = [];
	    for (key in object) {
		result.push(key);
	    }
	    return result.sort();
	}
    }
    var numKeys;
    if (Object.keys){
	numKeys = function(object) {
	    return Object.keys(object).length;
	}
    } else {
	numKeys = function(object) {
	    var result = 0;
	    for (key in object) {
		result++;
	    }
	    return result;
	}
    }
    var IKeys = keys.IKeys;
    function IObject(object,array,offset) {
	this.object = object;
	this.key = array[offset];
	this.value = object[this.key];
	IKeys.call(this,array,offset);
    }
    IKeys.prototype.mixin(IObject.prototype);
    IObject.prototype.tail = function() {
	if (!this.tail) {
	    this.tail = new IObject(this.object,this.array,this.offset+1);
	}
	return this.tail;
    }
    IObject.prototype.set = function(key,value) {
	var object = this.object;
	var keys = this.cons(key);
	var array = keys.array;
	var offset = keys.array;
	if (object[key] !== undefined) {
	    if (object[key] === value) { return this; }
	    var noo = {};
	    for (var i = offset; i < keys.length; i++) {
		noo[keys[i]] = object[keys[i]];
	    }
	    object = noo;
	}
	object[key] = value;
	return new IObject(object,array.offset);
    }
    IObject.prototype.get = function(key) {
	return this.object()[key];
    }
    IObject.prototype.map = function(fun) {
	var object = {};
	for (var i = this.offset; i < this.array.length; i++) {
	    var key = this.array[i];
	    object[key] = fun(this.object[key],key);
	}
	return new IObject(object,this.array,this.offset);
    }
    IObject.prototype.all = function(fun) {
	for (var i = this.offset; i < this.array.length; i++) {
	    if !(fun(this.object[key],key)) { return false; }
	}
	return true;
    }
    IObject.prototype.filter = function(fun) {
	return filter(fun,this.object());
    }
    IObject.prototype.object = function() {
	var object = this.object;
	var array = this.array;
	var offset = this.offset;
	if (numKeys(object) == array.length - offset) {
	    return object;
	} else {
	    var noo = {};
	    for (var i = offset; i < array.length; i++) {
		var key = array[i];
		noo[key] = object[key];
	    }
	    this.object = noo;
	    return noo;
	}
    }
    function map(fun,obj) {
	var noo = {};
	for (var key in obj) {
	    noo[key] = fun(obj[key],key);
	}
	return noo;
    }
    function all(fun,obj) {
	for (var key in obj) {
	    if (!fun(obj[key],key)) { return false; }
	}
	return true;
    }
    function filter(fun,obj) {
	var noo = {};
	for (var key in obj) {
	    if (fun(obj[key],key)) { noo[key] = obj[key]; }
	}
	return noo;
    }
    return {
	keys: keysOf,
	iobject: function(object) { return new IObject(object,keysOf(object),0); },
	lookup: function(object,key) { return box.box(object[key]); },
        map: map
    }
});