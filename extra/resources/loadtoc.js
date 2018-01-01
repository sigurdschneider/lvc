var items = $("<div id='stoc'></div>");
function processData(data, callback) {
    let toc = $(data).find("#toc");
    var cur = null;
    toc.children().each(function () {
	if ($(this).prop("tagName") == "A") {
	    let l = $(this).text();
	    let link = $(this).attr("href");
   	    if (cur) {
   		items.append(cur);
	    }
   	    cur = $("<div><a class='vfilelink'><h2 class='vfile'></h2></a><div id='toc'></div></div>");
	    cur.find(".vfile").html(l);
	    cur.find(".vfilelink").attr("href", link);
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
