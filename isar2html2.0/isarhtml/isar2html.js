class Isar2Html {
  
  static makeClickable(d) {
  
    d.onmouseover = function (e) {
      d.style.backgroundColor = "#FFFACD";
      d.style.cursor = "pointer";
    };
    
    d.onmouseout = function (e) {
      d.style.backgroundColor = "transparent";
      d.style.cursor = "default";
    };
    
    d.style.position = "relative";
    d.style.zIndex = 1;
  }
  
  static setupHideShow(id) {
    
    var hs = document.getElementById("hstrigger"+id);
    var c = document.getElementById("hscontent"+id);
    
    hs.onclick = function (evt) {
      if (c.style.display == "none")
        c.style.display = "block";
      else
        c.style.display = "none";
    };
    
    //makeClickable(hs);
    
    c.style.display = "none";
  }
  
  static getpos(obj) {
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
  
  
  static setupHints(id) {
    
    var href = document.getElementById("hintref"+id);
    var hrc = document.getElementById(href.innerHTML);
    
    hrc.style.display = "none";
    
    href.onclick = function (e) {
      if (hrc.style.display == "none") {
      
        var pos = Isar2Html.getpos(href);
        
        hrc.style.left = (pos[0] - 120) + "px";
        hrc.style.top = (pos[1] - 180) + "px";
        
        hrc.style.display = "block";
      }
      else
        hrc.style.display = "none";
    };
    
    Isar2Html.makeClickable(href);    
  }

  static main() {
    // set initial content
    var par_numblocks = document.getElementById("par_hstrigger");
    if( par_numblocks == null )
      alert("Number of blocks is unspecified");
    //par_numblocks.style.display = "none";
    
    var numblocks = parseInt(par_numblocks.innerHTML); 
    var i = 0;
    while( i < numblocks ) {
      Isar2Html.setupHideShow(i);
      i++;
    }
    
    var par_numhints = document.getElementById("par_hintref");
    if( par_numhints == null )
      alert("Number of hints is unspecified");
    //par_numhints.style.display = "none";
    
    var numhints = parseInt(par_numhints.innerHTML); 
    i = 0;
    while( i < numhints ) {
      Isar2Html.setupHints(i);
      i++;
    }
  }
}

// Run main when page loads
if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", Isar2Html.main);
} else {
  Isar2Html.main();
}