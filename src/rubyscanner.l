/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2008 by Dimitri van Heesch.
 *               2009      by Vincent Fourmond
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation under the terms of the GNU General Public License is hereby 
 * granted. No representations are made about the suitability of this software 
 * for any purpose. It is provided "as is" without express or implied warranty.
 * See the GNU General Public License for more details.
 *
 * Documents produced by Doxygen are derivative works derived from the
 * input used in their production; they are not affected by this license.
 *
 */
/*  This code is based on the work done by the MoxyPyDoxy team
 *  (Linda Leong, Mike Rivera, Kim Truong, and Gabriel Estrada)
 *  in Spring 2005 as part of CS 179E: Compiler Design Project
 *  at the University of California, Riverside; the course was
 *  taught by Peter H. Froehlich <phf@acm.org>.
 */

/*
 * This is the scanner for the Ruby language, but it is derived from the one
 * for the python language, hence the credits above.
 */

%{

/*
 *	includes
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <ctype.h>

#include "qtbc.h"
#include <qarray.h>
#include <qstack.h>
#include <qregexp.h>
#include <unistd.h>
#include <qfile.h>
#include <qfileinfo.h>
#include <qstack.h>
#include <qvaluestack.h>
  
#include "rubyscanner.h"
#include "entry.h"
#include "message.h"
#include "config.h"
#include "doxygen.h"
#include "util.h"
#include "defargs.h"
#include "language.h"
#include "commentscan.h"
// #include "pycode.h"

#define YY_NEVER_INTERACTIVE 1

/* -----------------------------------------------------------------
 *
 *	statics
 */

  
static ParserInterface *g_thisParser;
static const char *     inputString;
static int		inputPosition;
static QFile            inputFile;

static Protection	protection;

static Entry*		current_root = 0 ;
static Entry*		current      = 0 ;
static Entry*		previous     = 0 ;
static Entry*		bodyEntry    = 0 ;
static Entry*		global_root  = 0 ;

static int		yyLineNr     = 1 ;
static QCString		yyFileName;
static MethodTypes 	mtype;
static bool    		gstat;
static Specifier 	virt;

static QCString 	g_namespace_kind;

static int              docBlockContext;
static QCString         docBlock;
static QCString         docBlockName;
static bool             docBlockInBody;
static bool             docBlockJavaStyle;
static bool             docBrief;
static bool             docBlockSpecial;

static bool             g_doubleQuote;
static bool             g_specialBlock;
static int              g_stringContext;
static QGString *       g_copyString;
static int              g_indent = 0;
static int              g_curIndent = 0;

static QDict<QCString>  g_packageNameCache(257);
static QCString         g_packageScope;

static char             g_atomStart;
static char             g_atomEnd;
static int              g_atomCount;

//static bool             g_insideConstructor;

static QCString         g_packageName;

static bool             g_hideClassDocs;

static QCString         g_defVal;
static int              g_braceCount;

static bool             g_lexInit = FALSE;
static bool             g_packageCommentAllowed;

// For now, I can't say this is being used a lot ;-)...
// Push_pop start conditions
QValueStack<int>        g_sc_stack;

#define PUSH_SC(n) g_sc_stack.push(YY_START);BEGIN(n)
#define POP_SC { if(g_sc_stack.count()) BEGIN(g_sc_stack.pop()); \
	       	   else { printf("Out of SC stack ?? at %s:%d\n",  \
		   	    (const char *)yyFileName,yyLineNr);    \
			  BEGIN(Search);}}

/// \todo a configuration value should offer the possibility to prefer
/// a 'rdoc-compatible' mode where all comments are taken into
/// account, but a blank line discards previous contents, and a
/// 'normal' mode resembling the usual C++ one: nothing gets into the
/// documentatin unless you ask for it with a specific format of the
/// comments.

//////////////////////////////////////////////////////////////////////
// Bookkeeping

// Whether or not next end/def/class statement can be taken into account
static bool             g_statement_ok; // OK to start a statement ?
// OK to finish an "expression" on a newline (excludes opening if and so on)?
static bool 		g_can_end; 
static bool		g_absorb_string;
static void 		(*g_absorb_hook)();
static QCString		g_absorbed_string;

static void oneCharBookKeeping(char ch)
{
  // \todo: add a mechanism to require the "recording" of values to a string
  if(isalnum(ch) || ch == '_' || ch == '?' || ch == '!')
    g_statement_ok = FALSE;
  else
    g_statement_ok = TRUE;
  if(ch == '\n')
    yyLineNr++;
  if(strchr("*,+-/.\\", ch))
    g_can_end = FALSE;
  else
    g_can_end = TRUE;
  if(g_absorb_string)
    g_absorbed_string += ch;
//  if(g_absorb_string)
//    printf("Absorbing: %s\n", (const char*)g_absorbed_string);
}

// This function *must* be called at the end of every single rule !
static void bookKeeping()
{
  for( const char* c = yytext ; *c ; ++c )
    oneCharBookKeeping(*c);
}


//-----------------------------------------------------------------------------


static void initParser()
{
  protection = Public;
  mtype = Method;
  gstat = FALSE;
  virt = Normal;
  previous = 0;
  g_packageCommentAllowed = TRUE;
  g_packageNameCache.setAutoDelete(TRUE);
  g_statement_ok = TRUE;
  g_can_end = TRUE;
  g_absorb_string = FALSE;
  g_absorb_hook = 0;
}

static void initEntry()
{
  //current->python = TRUE;
  current->protection = protection ;
  current->mtype      = mtype;
  current->virt       = virt;
  current->stat       = gstat;
  current->objc       = FALSE; //insideObjC;
  current->setParent(current_root);
  initGroupInfo(current);
}

static void newEntry()
{
  previous = current;
  if(current_root != current)
    current_root->addSubEntry(current);
  current = new Entry ;
  initEntry();
}

//////////////////////////////////////////////////////////////////////
// Expression absorption

static QValueStack<const char *> g_expression_delimiters;
static bool 		         g_keep_last;

static void startAbsorbing(const char * delim, bool keep,
       	    		   void (*hook)() = 0)
{
  g_absorbed_string.resize(0);
  g_absorb_string = TRUE;
  g_absorb_hook = hook;
  g_expression_delimiters.clear();
  g_expression_delimiters.append(delim);
  g_keep_last = keep;
}

static void stopAbsorbing()
{
  g_expression_delimiters.clear();
  g_absorb_string = FALSE;
  if(g_absorb_hook)
    g_absorb_hook();
}

#define ABSORB_UNTIL(what, keep, hook) { startAbsorbing(what,keep,hook);      \
			PUSH_SC(AbsorbExpression);}

// To be used within an expression...
#define CONTINUE_UNTIL(what) { g_expression_delimiters.append(what); \
			PUSH_SC(AbsorbExpression);}



// Assign a default value to the argument of current.
static void assignDefaultValue()
{
  if(! g_absorbed_string.isEmpty() && current->argList->last()) {
    current->argList->last()->defval = 
      g_absorbed_string.stripWhiteSpace();
    g_absorbed_string.resize(0);
  }
}

// Assign a default value to the argument of current.
static void assignConstant()
{
  if(! g_absorbed_string.isEmpty()) {
    current->initializer = g_absorbed_string;
    printf("Assigned constant initial value: %s",
    	   (const char *) g_absorbed_string);
    g_absorbed_string.resize(0);
  }
  newEntry();
}

// In this function, we parse a list of strings or symbols to end
// up with a list of symbols.
static QValueList<QCString> parseSymbols(QCString s)
{
  QString str = s;
  int idx,len;
  QRegExp resym("[^:,'\" \t\n]+");
  QValueList<QCString> symbols;
  // Black magic, as for some reason the code below does not
  // work if that isn't here...
  const char * b = (const char *) str.local8Bit();
  while((idx = resym.match(str, idx, &len))>=0) {
    // printf("Match: %s %d %d\n", (const char*) str.local8Bit(),
    // 	   idx, len);
    QCString sym = str.mid(idx, len).local8Bit();
    symbols.append(sym);
    idx+=len;
  }
  return symbols;
}


static QCString g_attribute_function;

// Assign a default value to the argument of current.
static void doAttributes()
{
  if(! g_absorbed_string.isEmpty()) {
    int attr;
    if(g_attribute_function.contains("attr_accessor"))
      attr = Entry::Readable|Entry::Writable;
    else if (g_attribute_function.contains("attr_writer"))
      attr = Entry::Writable;
    else if (g_attribute_function.contains("attr_writer"))
      attr = Entry::Readable;
    else {
      printf("Attribute function not understood: %s\n",
	     (const char *) g_attribute_function);
      attr = 0;
    }
      
    QValueList<QCString> symbols = 
      parseSymbols(g_absorbed_string);
    for(int i = 0; i < symbols.count(); i++) {
      current->name = symbols[i];
      current->protection = Public;
      current->fileName  = yyFileName;
      current->startLine = yyLineNr;
      current->bodyLine  = yyLineNr;
      current->section = Entry::VARIABLE_SEC;
      current->spec = attr;
      newEntry();
    }
    g_absorbed_string.resize(0);
  }
}

/// Enters a new namespace, creating it based on the current entry
/// if it does not exist, or merely copying its documentation to the
/// current definition if it does. The name is relative to the current
/// namespace
static void enterNamespace(QCString name, QCString type)
{
  Entry * ns = 0;
  QCString baseName = current_root->name;
  if(! baseName.isEmpty())
    baseName += "::";
  /// We first look for a namespace of the like in current_root
  for(int i = 0; i < current_root->children()->count(); i++) {
    Entry * entry = const_cast<QList<Entry> *>(current_root->children())->at(i);
    if(entry->section & Entry::SCOPE_MASK)
      if((!entry->name.isEmpty()) && entry->name == (baseName + name)) {
        ns = entry;
    	break;
      }
  }
  
  if(ns) { 
    if(ns->type != type) 
      fprintf(stderr, "Warning: %s was declared as %s but now as %s\n",
      	      (const char *) ns->name,
      	      (const char *)ns->type, (const char *)type);
    current->reset();
  }
  else {
    current->section = Entry::SCOPE_MASK;
    current->argList->clear();
    current->type == type ;
    current->fileName  = yyFileName;
    current->bodyLine  = yyLineNr;
    current->name = baseName + name;
    g_packageCommentAllowed = FALSE;
    ns = current;
    newEntry();
  }

  groupEnterCompound(yyFileName,yyLineNr,baseName + name);
  
  if(ns->parent() != current_root)
    printf("Not automatically setting parent !\n");
  current_root = ns;
}



static void leaveNamespace()
{
  if(current_root != global_root) {
    current_root = current_root->parent();
    groupLeaveCompound(yyFileName,yyLineNr,"");
  }
  else {
    fprintf(stderr, "Warning: attempting to end root namespace at %s:"
    "%d\n\%s\n",
            (const char*)yyFileName,yyLineNr, yytext);
  }
}


static QCString findPackageScopeFromPath(const QCString &path)
{
  QCString *pScope = g_packageNameCache.find(path);
  if (pScope)
  {
    return *pScope;
  }
  QFileInfo pf(path+"/__init__.py"); // found package initialization file
  if (pf.exists())
  {
    int i=path.findRev('/');
    if (i!=-1)
    {
      QCString scope = findPackageScopeFromPath(path.left(i));
      if (!scope.isEmpty())
      {
	scope+="::";
      }
      scope+=path.mid(i+1);
      g_packageNameCache.insert(path,new QCString(scope));
      return scope;
    }
  }
  return "";
}
  
static QCString findPackageScope(const char *fileName)
{
  if (fileName==0) return "";
  QFileInfo fi(fileName);
  return findPackageScopeFromPath(fi.dirPath(TRUE).data());
}

//-----------------------------------------------------------------
static void startCommentBlock(bool brief)
{
  if (brief)
  {
    current->briefFile = yyFileName;
    current->briefLine = yyLineNr;
  }
  else
  {
    current->docFile = yyFileName;
    current->docLine = yyLineNr;
  }
}

/*
static void appendDocBlock() {
  previous = current;
  current_root->addSubEntry(current);
  current = new Entry;
  initEntry();
}
*/

static void handleCommentBlock(const QCString &doc,bool brief)
{
  /// \todo here should come a basic rdoc-style pre-parsing of
  /// comments, only triggered when 
  int position = 0;
  bool needsEntry;
  while (parseCommentBlock(g_thisParser,
	  (docBlockInBody && previous) ? previous : current,
	  doc,     // text
	  yyFileName, // file
	  brief ? current->briefLine : current->docLine,   // line of block start
	  docBlockInBody ? FALSE : brief, 
          docBlockJavaStyle, // javadoc style // or FALSE,
	  docBlockInBody,
	  protection,
          position,
          needsEntry)
     ) // need to start a new entry
  {
    if (needsEntry)
    {
      newEntry();
    }
  }
  if (needsEntry)
  {
    newEntry();
  }
}

static void endOfDef()
{
  if (bodyEntry)
  {
    bodyEntry->endBodyLine  = yyLineNr;
    bodyEntry = 0;
  }
  newEntry();
  //g_insideConstructor = FALSE;
}

static inline void addToString(const char *s)
{
  if (g_copyString) (*g_copyString)+=s;
}

static void initTriDoubleQuoteBlock()
{
  docBlockContext   = YY_START;
  docBlockInBody    = FALSE;
  docBlockJavaStyle = TRUE;
  docBlockSpecial   = yytext[3]=='!';
  docBlock.resize(0);
  g_doubleQuote = TRUE;
  startCommentBlock(FALSE);
}

static void initTriSingleQuoteBlock()
{
  docBlockContext   = YY_START;
  docBlockInBody    = FALSE;
  docBlockJavaStyle = TRUE;
  docBlockSpecial   = yytext[3]=='!';
  docBlock.resize(0);
  g_doubleQuote = FALSE;
  startCommentBlock(FALSE);
}

static void initSpecialBlock()
{
  docBlockContext   = YY_START;
  docBlockInBody    = FALSE;
  docBlockJavaStyle = TRUE;
  docBrief = TRUE;
  docBlock.resize(0);
  startCommentBlock(TRUE);
}

//-----------------------------------------------------------------------------
/* ----------------------------------------------------------------- */
#undef	YY_INPUT
#define	YY_INPUT(buf,result,max_size) result=yyread(buf,max_size);

static int yyread(char *buf,int max_size)
{
  int c=0;
  while ( c < max_size && inputString[inputPosition] )
  {
    *buf = inputString[inputPosition++] ;
    //printf("%d (%c)\n",*buf,*buf);
    c++; buf++;
  }
  return c;
}

%}

       /* start command character */



BB                [ \t]+
B                 [ \t]*
NEWLINE           \n
BN                [ \t\n]
BLANK		  [[:space:]]*

DIGIT             [0-9]
LETTER            [A-Za-z]
CAPITAL           [A-Z]


EXPCHAR           [#(){}\[\],:.%/\\=`*~|&<>!;+-]
CONSTNAME         {CAPITAL}({LETTER}|{DIGIT}|"_")*
IDENTIFIER        ({LETTER}|"_")({LETTER}|{DIGIT}|"_")*
FUNCNAME          {IDENTIFIER}([?!]|{B}=)?
PARAMNAME         ([*&]{B})?{IDENTIFIER}
SCOPE             {CONSTNAME}("(::\.)"{CONSTNAME})*
BORDER            ([^A-Za-z0-9])

      /* limit of a word */
WLIM   	  	  [^[:alnum:]!?_]

      /* all the things which start a block that must terminate with end */

EBLOCK	     	  begin|if|while|until|unless|proc|do|for|def|module|class

STARTDOCSYMS      ^{B}"#"#*
POUNDCOMMENT      {B}"#"[^#\n][^\n]* 

     /* attribute specifiers */

ATTR_SPEC	  attr_(accessor|writer|reader)

/* emacs, please stop parsing ' */

%option noyywrap

  /* Main search state: current_root must be a namespace then */

%x Search

  /* Various slurp states */
  /* -> until a closing 'end' statement */
%x SlurpUntilEnd

  /* Mid-comment states */

%x SpecialComment

  /* Function states */

%x FunctionDec
%x FunctionParams

  /* Class states */

%x ClassDec

  /* Variable states */

  /* String states */

%x SingleQuotedString
%x DoubleQuotedString

  /* expression state */

%x AbsorbExpression

  /* import */

  /* todo: an absorbVal state !*/

%%



  /* ------------ String Catchalls  -------------- */
<Search,SlurpUntilEnd,AbsorbExpression>{
  "'"		      {
  		        PUSH_SC(SingleQuotedString);
			bookKeeping();
		      }

  \" 		      {
  		        PUSH_SC(DoubleQuotedString);
			bookKeeping();
		      }
}

  /* ------------ Main search state  -------------- */
<Search>{

  (class|module)/{WLIM} { // class definition
  			  // todo: here, a class can be followed by <<
			if(g_statement_ok) {
			  g_namespace_kind =
    			  QCString(yytext).stripWhiteSpace();
			  BEGIN(ClassDec);
			}
			bookKeeping();
    		      }

  "def"{BB}           { // start of a function/method definition
	      	        if(g_statement_ok) {
			  current->fileName  = yyFileName;
			  current->startLine = yyLineNr;
			  current->bodyLine  = yyLineNr;
			  current->section = Entry::FUNCTION_SEC;
			  current->protection = Public;
			  current->objc = FALSE;
			  current->virt = Normal;
			  current->stat = FALSE;
			  current->mtype = mtype = Method;
			  current->type = "def";
			  current->name.resize(0);
			  current->args.resize(0);
			  current->argList->clear();
			  g_packageCommentAllowed = FALSE;
			  docBlockInBody = FALSE;
			  BEGIN( FunctionDec );
			}
			bookKeeping();
                      }

  "end"               {
  		        if(g_statement_ok)
  		          leaveNamespace();
			bookKeeping();
		      }	

  {STARTDOCSYMS}      {
  		      	g_packageCommentAllowed = FALSE;
			initSpecialBlock();
			BEGIN(SpecialComment);
			bookKeeping();
                      }

  {CONSTNAME}{B}=     { // A constant definition
  		      	QCString name(yytext);
			name.resize(name.size() - 1);
  		        current->name = name.stripWhiteSpace();
			current->protection = Public;
			current->fileName  = yyFileName;
			current->startLine = yyLineNr;
			current->bodyLine  = yyLineNr;
			current->section = Entry::VARIABLE_SEC;
			current->spec = Entry::Initonly;
			bookKeeping();
			ABSORB_UNTIL("\n;",FALSE, assignConstant);
  		      }

  {ATTR_SPEC}/{WLIM}  {
  		        g_attribute_function = 
			  QCString(yytext).stripWhiteSpace();
  		        bookKeeping();
		        ABSORB_UNTIL("\n;",FALSE, doAttributes);
  		      }

%{
/* this should be enabled again if STARTDOCSYMS should include two ##
   again -- but I don't think it should be the case, as compatibility
   with rdoc is a good thing (TM)
 */
/*
  {POUNDCOMMENT}      {
  		        printf("Pound comment: '%s'\n", yytext);
  		      	g_packageCommentAllowed = FALSE;
  		      }
*/
%}

  .                   { // any other character...
                        // This is the major default
                        // that should catch everything
                        // else in Body.
			bookKeeping();
                      }

  {NEWLINE}           {
  		        bookKeeping();
  		      }


}

<SpecialComment>{
    ^{B}"#"("#")*      { // skip leading hashes
			bookKeeping();
      		      }
    \n/{B}"#"	      { // continuation of the comment on the next line
      		        docBlock+='\n';
			docBrief = FALSE;
                        startCommentBlock(FALSE);
			bookKeeping();
      		      }
    [^#\n]+           { // any other stuff
      			docBlock+=yytext;
			bookKeeping();
      		      }
    \n		      { // new line that ends the comment
		        handleCommentBlock(docBlock, docBrief);
			BEGIN(docBlockContext);
			bookKeeping();
      		      }
    .		      { // anything we missed
      		        docBlock += *yytext;
			bookKeeping();
      		      }
}


  /* When in this state, we ignore everything until the matching end */
<SlurpUntilEnd>{
  "end"/{WLIM}        {	
  		        if(g_statement_ok) {
			  POP_SC;
			}
			bookKeeping();
		      }

  {STARTDOCSYMS}      {
                        printf("Starting special comment inside block\n");
  		      	g_packageCommentAllowed = FALSE;
			initSpecialBlock();
			BEGIN(SpecialComment);
			docBlockInBody = TRUE;
			bookKeeping();
                      }

  {EBLOCK}/{WLIM}    {
  			if(g_statement_ok) {
			  PUSH_SC(SlurpUntilEnd);
                        }
			bookKeeping();
		      }

  {NEWLINE}           {
  		        bookKeeping();
  		      }


  .                   { 
  		        // printf("Slurping: '%s'\n", yytext);
  		        bookKeeping();
                      }


}

<ClassDec>{

  {CONSTNAME}/{B}<{B}{CONSTNAME} {
  			// the name of the class, we can enter 
  		        // the namespace now
			// TODO: handle the case of anonymous classes.
			enterNamespace(QCString(yytext).stripWhiteSpace(),
				       g_namespace_kind);
			if(current_root->name.contains("Exception"))
			  current_root->spec |= Entry::Exception;
  		        bookKeeping();
                      }

  {B}<{BLANK}{SCOPE}  {
			// Now, we have found some class
			QCString base = QCString(yytext).stripWhiteSpace();
			base.remove(0,1); // remove initial stuff
			// Note that current_root is now the class
			current_root->extends
			  ->append(new BaseInfo(base.stripWhiteSpace(),
			  	       Public,Normal));
			if(base.contains("Exception"))
			  current_root->spec |= Entry::Exception;
			// We will try to look for exceptions
                        BEGIN(Search);
  		        bookKeeping();
  		      }
		      

  {CONSTNAME} { 
  		      	// Todo: handle the case of a scope ????
  		        enterNamespace(QCString(yytext).stripWhiteSpace(),
				       g_namespace_kind);
                        // For now, no parsing of inheritance...
                        BEGIN(Search);
  		        bookKeeping();
                      }

  [[:space:]]         { 
  		        bookKeeping();
                      }
  "<<"		      {
			printf("Warning: ignoring anonymous class in "
			       "%s:%d\n",
			       (const char *) yyFileName,
			       yyLineNr);
			bookKeeping();
			BEGIN(Search); // to make sure PUSH_SC comes back to Search
			PUSH_SC(SlurpUntilEnd);
  		      }
  

  .                   { 
  		        printf("Warning: garbage '%s' in class "
  		               "definition in %s:%d\n",
			       yytext,
			       (const char *) yyFileName,
			       yyLineNr);

  		        bookKeeping();
                      }
}

<FunctionDec>{
  ({CONSTNAME}|self)\.  { // this is a class function
  			current->stat = TRUE;
			bookKeeping();
  		      }

  {FUNCNAME}          {
		        //found function name
			current->name = yytext;
			bookKeeping();
                      }

  {B}[\n;]   	      { // function without arguments
			newEntry();
			BEGIN(Search); // come back to Search after slurping
			PUSH_SC(SlurpUntilEnd);			
			bookKeeping();
		      }

  {B}"("              {
			BEGIN(FunctionParams);
			bookKeeping();
		      }


  .                   { 
  		        printf("Warning: garbage '%s' in function "
  		               "definition in %s:%d\n",
			       yytext,
			       (const char *) yyFileName,
			       yyLineNr);
  		        bookKeeping();
                      }

}

  /* function parameters */

<FunctionParams>{
  ","		      { 
  		        bookKeeping();	 
                      }

  {PARAMNAME}         { // Name of parameter
			Argument *a = new Argument;
			printf("Found argument: %s\n",
			       yytext);
			current->argList->append(a);
			current->argList->getLast()->name = 
			  QCString(yytext).stripWhiteSpace();
			current->argList->getLast()->type = "";
    		        bookKeeping();	 
                      }

  {BB}		      {
  		        bookKeeping();
  		      }

  ")"		      {
			newEntry();
			BEGIN(Search); // come back to Search after slurping
			PUSH_SC(SlurpUntilEnd);			
    		        bookKeeping();	 
  		      }

  "="		      {
  		        bookKeeping(); // must be done before, for once ;-) !
			ABSORB_UNTIL(",)",TRUE, assignDefaultValue);
  		      }

  .                   { 
  		        printf("Warning: garbage '%s' in function "
  		               "parameters in %s:%d\n",
			       yytext,
			       (const char *) yyFileName,
			       yyLineNr);
  		        bookKeeping();
                      }

}

<AbsorbExpression>{
  {EBLOCK}/{WLIM}     {
  			if(g_statement_ok) {
			  PUSH_SC(SlurpUntilEnd);
                        }
			bookKeeping();
		      }
  "{"		      {
  		        CONTINUE_UNTIL("}");
			bookKeeping();
  		      }
  "["		      {
  		        CONTINUE_UNTIL("]");
			bookKeeping();
  		      }

  "("		      {
  		        CONTINUE_UNTIL(")");
			bookKeeping();
  		      }

  .|\n		      {
  		        if(g_can_end && 
			  strchr(g_expression_delimiters.last(),*yytext)) {
			  if(g_expression_delimiters.count() == 1) {
  		            stopAbsorbing();
			    if(g_keep_last)
			      yyless(0); // and we push back
			    else
			      bookKeeping();
                          }
			  else {
			    g_expression_delimiters.pop();
			    bookKeeping();
			  }
  		          POP_SC;
			}
			else
			  bookKeeping();
		      }

}

  /* now, handling quotes */

<SingleQuotedString>{

  "'"		      {
  		        POP_SC;
			bookKeeping();
		      }

  [^']		      {
			bookKeeping();
		      }


}


  /* Todo: this should be handling as well the #{ ... } 
     substitution that can contain arbitraty code, such as
     "end", for instance.
  */

<DoubleQuotedString>{

  \\\"		      {
  		        bookKeeping();
  		      }

  \"		      {
  		        POP_SC;
			bookKeeping();
  		      }

  [^"]		      {
			bookKeeping();
		      }

}




%%

//----------------------------------------------------------------------------


//----------------------------------------------------------------------------


static void parseMain(const char *fileName,const char *fileBuf,Entry *rt)
{
  initParser();

  inputString = fileBuf;
  inputPosition = 0;

  protection    = Public;
  mtype         = Method;
  gstat         = FALSE;
  virt          = Normal;
  current_root  = rt;
  // The upper limit: we won't back up more than this.
  global_root   = rt;
  g_specialBlock = FALSE;


  inputFile.setName(fileName);
  if (inputFile.open(IO_ReadOnly))
  {
    yyLineNr= 1 ; 
    yyFileName = fileName;
    //setContext();
    msg("Parsing file %s...\n",yyFileName.data());

    QFileInfo fi(fileName);
    QString baseName=fi.baseName();

    current            = new Entry;
    current->name      = "";
    current->section   = Entry::NAMESPACE_SEC;
    current->type      = "namespace";
    current->fileName  = yyFileName;
    current->startLine = yyLineNr;
    current->bodyLine  = yyLineNr;

    rt->addSubEntry(current);

    // I don't think we need every single entry to be within a file
    // namespace ?
    // current_root  = current ;
    initParser();
    current       = new Entry;

    groupEnterFile(yyFileName,yyLineNr);
    
    current->reset();
    rubyscanYYrestart( rubyscanYYin );
    BEGIN( Search );
    rubyscanYYlex();
    g_lexInit=TRUE;

    groupLeaveFile(yyFileName,yyLineNr);

    global_root->program.resize(0);
    delete current; current=0;

    // parseCompounds(current_root);

    inputFile.close();
  }
  
}

//----------------------------------------------------------------------------

static void parsePrototype(const QCString &text)
{
  //printf("**** parsePrototype(%s) begin\n",text.data());
  if (text.isEmpty()) 
  {
    warn(yyFileName,yyLineNr,"Empty prototype found!");
    return;
  }

  g_specialBlock = FALSE;
  g_packageCommentAllowed = FALSE;

  const char *orgInputString;
  int orgInputPosition;
  YY_BUFFER_STATE orgState;
  
  // save scanner state
  orgState = YY_CURRENT_BUFFER;
  yy_switch_to_buffer(yy_create_buffer(rubyscanYYin, YY_BUF_SIZE));
  orgInputString = inputString; 
  orgInputPosition = inputPosition;

  // set new string
  inputString = text;
  inputPosition = 0;
  rubyscanYYrestart( rubyscanYYin );

  // TODO
  // BEGIN( FunctionDec );

  rubyscanYYlex();
  g_lexInit=TRUE;

  current->name = current->name.stripWhiteSpace();
  if (current->section == Entry::MEMBERDOC_SEC && current->args.isEmpty())
    current->section = Entry::VARIABLEDOC_SEC;

  // restore original scanner state

  YY_BUFFER_STATE tmpBuf = YY_CURRENT_BUFFER;
  yy_switch_to_buffer(orgState);
  yy_delete_buffer(tmpBuf);

  inputString = orgInputString; 
  inputPosition = orgInputPosition;

  //printf("**** parsePrototype end\n");
}

void rubyscanFreeScanner()
{
#if defined(YY_FLEX_SUBMINOR_VERSION) 
  if (g_lexInit)
  {
    rubyscanYYlex_destroy();
  }
#endif
}

// Quickly dumps an entry and all its children to standard output
// For debugging purposes, obviously.
void dumpEntry(Entry *entry, int indentation)
{
  char buffer[40];
  for(int i = 0; i < indentation; i++)
    buffer[i] = ' ';
  buffer[indentation] = 0;
  printf("%s%s: type %s, section 0x%x\tfile: %s (%d children)\n", buffer, 
  	  (const char*)entry->name, 
  	  (const char*)entry->type, 
	  entry->section,
  	  (const char*)entry->fileName,
	  entry->children()->count());
  for(int i = 0; i < entry->children()->count(); i++)
    dumpEntry(const_cast<QList<Entry> *>(entry->children())->at(i), indentation+2);
}

//----------------------------------------------------------------------------

void RubyLanguageScanner::parseInput(const char *fileName,const char *fileBuf,Entry *root)
{
  g_thisParser = this;
  ::parseMain(fileName,fileBuf,root);
  // For now, we need the debugging information:
  // printf("Dumping root %p\n", root);
  // dumpEntry(root, 0);
}

bool RubyLanguageScanner::needsPreprocessing(const QCString &)
{
  return FALSE;
}

void RubyLanguageScanner::parseCode(CodeOutputInterface &codeOutIntf,
    const char *scopeName,
    const QCString &input,
    bool isExampleBlock,
    const char *exampleName,
    FileDef *fileDef,
    int startLine,
    int endLine,
    bool inlineFragment,
    MemberDef *memberDef
    )
{
  // ::parsePythonCode(codeOutIntf,scopeName,input,isExampleBlock,exampleName,
  //                   fileDef,startLine,endLine,inlineFragment,memberDef);
  /** 
      \todo Write a code scanner, when I know how to write one.
  */
}

void RubyLanguageScanner::parsePrototype(const char *text)
{
  ::parsePrototype(text);

}

void RubyLanguageScanner::resetCodeParserState()
{
  
  // ::resetRubyCodeParserState();
  /** 
      \todo Write a code scanner, when I know how to write one.
  */
}

//----------------------------------------------------------------------------

#if !defined(YY_FLEX_SUBMINOR_VERSION) 
//----------------------------------------------------------------------------
extern "C" { // some bogus code to keep the compiler happy
  void rubyscannerYYdummy() { yy_flex_realloc(0,0); } 
}
#endif

