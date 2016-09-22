var items = $("<div id='stoc'></div>");
function processData(data, callback) {
    var toc = $(data).find("#toc");
    var cur = null;
    toc.children().each(function () {
	if ($(this).prop("tagName") == "A") {
	    let l = $(this).text();
   	    if (cur) {
   		items.append(cur);
	    }
   	    cur = $("<div><h2 class='vfile'></h2><div id='toc'></div></div>");
	    cur.children(".vfile").html(l);
	} else {
	    cur.children("#toc").append($(this));
	}
    });
    items.append(cur);
    callback();
}

function loadToC(callback) {
    var client = new XMLHttpRequest();
    client.open("GET", "toc.html", true);
    client.onreadystatechange = function () {
	if (client.readyState == 4) {
	    processData(this.responseText, callback);
	}
    }
    client.send();
}

function tocmodules(regex) {
    var l = items.children().filter( function() {
	return (regex.test($(this).find("h2.vfile").text()));
    });
//    console.log(l);
    return l;
}
