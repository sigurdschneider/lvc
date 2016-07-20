
File 
  = "COQAUX1" . hash:Hash . filename:Filename '\n'
    entries:(Entry*) { return [hash, filename, entries] }
 
Entry
  = num1:Integer . num2:Integer . id:Identifier . data:Data _ {return [num1, num2, id, data]}
  
Hash 
  = [0123456789abcdef]* { return text() }
  
Data 
  = [^\n]* { var t = text();
             t = t.substring(1, t.length-1);
             var v = parseFloat(t);
             return isNaN(v) ? t : v }
  
Filename
  = [^\n]* { return text() }
  
Identifier "identifier" 
  = [a-zA-Z_]+ { return text() }
  
Integer "integer"
  = [0-9]+ { return parseInt(text(), 10); }

_ "whitespace"
  = [ \t\n\r]*
