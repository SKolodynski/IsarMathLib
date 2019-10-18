import js.Dom;

class Isar2Html {
	
	static function makeClickable(d:HtmlDom) {
	
		d.onmouseover = function (e:Event) {
			d.style.backgroundColor = "#FFFACD";
			d.style.cursor = "pointer";
		}
		
		d.onmouseout = function (e:Event) {
			d.style.backgroundColor = "transparent";
			d.style.cursor = "default";
		}
		
		d.style.position = "relative";
		d.style.zIndex = 1;
	}
	
	static function setupHideShow(id:Int) {
		
		var hs = js.Lib.document.getElementById("hstrigger"+id);
		var c = js.Lib.document.getElementById("hscontent"+id);
		
		hs.onclick = function (evt) {
			if (c.style.display == "none")
				c.style.display = "block";
			else
				c.style.display = "none";
		}
		
		//makeClickable(hs);
		
		c.style.display = "none";
	}
	
	static function getpos(obj: HtmlDom) : Array<Int> {
		var curleft = 0;
		var curtop = 0;
		
		if (obj.offsetParent != null) {
			do {
				curleft += obj.offsetLeft;
				curtop += obj.offsetTop;
				obj = obj.offsetParent;
			} while (obj != null);
		}
		
		return [curleft,curtop];

	}
	
	
	static function setupHints(id:Int) {
		
		var href = js.Lib.document.getElementById("hintref"+id);
		var hrc = js.Lib.document.getElementById(href.innerHTML);
		
		hrc.style.display = "none";
		
		href.onclick = function (e:Event) {
			if (hrc.style.display == "none") {
			
				var pos = getpos(href);
				
				hrc.style.left = (pos[0] - 120) + "px";
				hrc.style.top = (pos[1] - 180) + "px";
				
				hrc.style.display = "block";
			}
			else
				hrc.style.display = "none";
		}
		
		makeClickable(href);		
	}

    static function main() {
        // set initial content
		var par_numblocks = js.Lib.document.getElementById("par_hstrigger");
		if( par_numblocks == null )
            js.Lib.alert("Number of blocks is unspecified");
		//par_numblocks.style.display = "none";
		
		var numblocks:Int = Std.parseInt(par_numblocks.innerHTML); 
		var i:Int = 0;
		while( i < numblocks ) {
			setupHideShow(i);
			i++;
		}
		
		var par_numhints = js.Lib.document.getElementById("par_hintref");
		if( par_numhints == null )
            js.Lib.alert("Number of hints is unspecified");
		//par_numhints.style.display = "none";
		
		var numhints:Int = Std.parseInt(par_numhints.innerHTML); 
		i = 0;
		while( i < numhints ) {
			setupHints(i);
			i++;
		}
    }
}
