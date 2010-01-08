/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2008 by Dimitri van Heesch.
 *               2009 by Vincent Fourmond
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


%{

#include <stdio.h>
#include <qvaluestack.h>

#include "rubycode.h"
#include "rubyscanner.h"
#include "message.h"

#include "scanner.h"
#include "entry.h"
#include "doxygen.h"
#include "outputlist.h"
#include "util.h"
#include "membername.h"
#include "searchindex.h"

#define YY_NEVER_INTERACTIVE 1

static ClassSDict    g_codeClassSDict(17);
static QCString      g_curClassName;
static QStrList      g_curClassBases;


static CodeOutputInterface * g_code;
static const char *  g_inputString;     //!< the code fragment as text
static int	     g_inputPosition;   //!< read offset during parsing 
static const char *  g_currentFontClass;
static bool          g_needsTermination;
static int           g_inputLines;      //!< number of line in the code fragment
static int	     g_yyLineNr;        //!< current line number
static FileDef *     g_sourceFileDef;
static Definition *  g_currentDefinition;
static MemberDef *   g_currentMemberDef;
static bool          g_includeCodeFragment;
static QCString      g_realScope;
static bool          g_insideBody;
static int           g_bodyCurlyCount;
static bool          g_searchingForBody;
static QCString      g_classScope;
static int           g_paramParens;
//static int           g_anchorCount;

static bool          g_exampleBlock;
static QCString      g_exampleName;
static QCString      g_exampleFile;

static QCString      g_type;
static QCString      g_name;

static bool          g_doubleStringIsDoc;

// Push/pop start conditions
static QValueStack<int>     g_sc_stack;

#define PUSH_SC(n) g_sc_stack.push(YY_START);BEGIN(n)
#define POP_SC { if(g_sc_stack.count()) BEGIN(g_sc_stack.pop()); \
	       	   else { BEGIN(Outer);}}

static QCString         g_heredoc_marker;
static bool 		g_pending_heredoc;
static int 		hereDocContext;

/// The context
static RubyLanguageScanner::ScannerContext context;

static void oneCharBookKeeping(char ch)
{
  context.parseOneChar(ch);
  if(ch == '\n') {
    if(g_pending_heredoc) {
      PUSH_SC(hereDocContext);
      g_pending_heredoc = FALSE;
    }
  }
}

// This function *must* be called at the end of every single rule !
static void bookKeeping()
{
  // printf("Doing bookkeeping of '%s'\n", yytext);
  for( const char* c = yytext ; *c ; ++c )
    oneCharBookKeeping(*c);
}



/// The nested scopes around the thing
static QValueStack<QCString>  nestedScopes;

static QValueStack<uint> g_indents;  //!< Tracks indentation levels for scoping in python

static void endFontClass();
// static void adjustScopesAndSuites(unsigned indentLength);

static void enterScope(const char *sc)
{
  nestedScopes.push(sc);
}

static void leaveScope()
{
  nestedScopes.pop();
}

static NamespaceDef * findNameSpace(const char * name)
{
  QCString n = name;
  NamespaceDef * d = 0;
  for(int i = nestedScopes.count(); i >= 0; i--) {
    d = getResolvedNamespace((const char*)n);
    if(d)
      break;
    if(i)
      n = nestedScopes[i - 1] + "::" + n;
  }
  return d;
}


/*! Represents a stack of variable to class mappings as found in the
 *  code. Each scope is enclosed in pushScope() and popScope() calls.
 *  Variables are added by calling addVariables() and one can search
 *  for variable using findVariable().
 */
class RubyVariableContext 
{
  public:
    static const ClassDef *dummyContext;    
    class Scope : public SDict<ClassDef> 
    {
      public:
	Scope() : SDict<ClassDef>(17) {}
    };
    
    RubyVariableContext() 
    {
      m_scopes.setAutoDelete(TRUE);
    }

    virtual ~RubyVariableContext() 
    {
    }
    
    void pushScope() 
    {
      m_scopes.append(new Scope);
    }

    void popScope() 
    {
      if (m_scopes.count()>0) 
      {
	m_scopes.remove(m_scopes.count()-1);
      }
    }

    void clear() 
    {
      m_scopes.clear();
      m_globalScope.clear();
    }

    void clearExceptGlobal() 
    {
      m_scopes.clear();
    }

    void addVariable(const QCString &type,const QCString &name);
    ClassDef *findVariable(const QCString &name);
    
  private:
    Scope        m_globalScope;
    QList<Scope> m_scopes;
};

void RubyVariableContext::addVariable(const QCString &type,const QCString &name)
{
  //printf("RubyVariableContext::addVariable(%s,%s)\n",type.data(),name.data());
  QCString ltype = type.simplifyWhiteSpace();
  QCString lname = name.simplifyWhiteSpace();

  Scope *scope = m_scopes.count()==0 ? &m_globalScope : m_scopes.getLast();
  ClassDef *varType;
  if (
      (varType=g_codeClassSDict[ltype]) ||  // look for class definitions inside the code block
      (varType=getResolvedClass(g_currentDefinition,g_sourceFileDef,ltype)) // look for global class definitions
     ) 
  {
    scope->append(lname,varType); // add it to a list
  }
  else 
  {
    if (m_scopes.count()>0) // for local variables add a dummy entry so the name 
                            // is hidden to avoid FALSE links to global variables with the same name
                            // TODO: make this work for namespaces as well!
    {
      scope->append(lname,dummyContext);
    }
  }
}

ClassDef *RubyVariableContext::findVariable(const QCString &name)
{
  if (name.isEmpty()) return 0;
  ClassDef *result = 0;
  QListIterator<Scope> sli(m_scopes);
  Scope *scope;
  // search from inner to outer scope
  for (sli.toLast();(scope=sli.current());--sli)
  {
    result = scope->find(name);
    if (result) 
    {
      return result;
    }
  }
  // nothing found -> also try the global scope
  result=m_globalScope.find(name);
  return result;
}

static RubyVariableContext g_theVarContext;
const ClassDef *RubyVariableContext::dummyContext = (ClassDef*)0x8;

class RubyCallContext
{
  public:
    struct Ctx
    {
      Ctx() : name(g_name), type(g_type), cd(0) {}
      QCString name;
      QCString type;
      ClassDef *cd;
    };

    RubyCallContext() 
    {
      m_classList.append(new Ctx);
      m_classList.setAutoDelete(TRUE);
    }

    virtual ~RubyCallContext() {}

    void setClass(ClassDef *cd)
    {
      Ctx *ctx = m_classList.getLast();
      if (ctx) 
      {
        ctx->cd=cd;
      }
    }
    void pushScope()
    {
      m_classList.append(new Ctx);
    }

    void popScope()
    {
      if (m_classList.count()>1)
      {
	Ctx *ctx = m_classList.getLast();
	if (ctx)
	{
	  g_name = ctx->name;
	  g_type = ctx->type;
	}
	m_classList.removeLast();
      }
      else
      {
      }
    }

    void clear()
    {
      m_classList.clear();
      m_classList.append(new Ctx);
    }

    ClassDef *getClass() const
    {
      Ctx *ctx = m_classList.getLast();

      if (ctx)
        return ctx->cd;
      else
        return 0;
    }

  private:
    QList<Ctx> m_classList;    
};

static RubyCallContext g_theCallContext;


/*! counts the number of lines in the input */
static int countLines()
{
  const char *p=g_inputString;
  char c;
  int count=1;
  while ((c=*p)) 
  { 
    p++ ; 
    if (c=='\n') count++;  
  }
  if (p>g_inputString && *(p-1)!='\n') 
  { // last line does not end with a \n, so we add an extra
    // line and explicitly terminate the line after parsing.
    count++, 
    g_needsTermination=TRUE; 
  } 
  return count;
}

static void setCurrentDoc(const QCString &name,const QCString &base,const QCString &anchor="")
{
  (void)name;
  (void)base;
  (void)anchor;
  //static bool searchEngineEnabled=Config_getBool("SEARCHENGINE");
  //if (searchEngineEnabled)
  //{
  //  Doxygen::searchIndex->setCurrentDoc(name,base,anchor);
  //}
}

static void addToSearchIndex(const char *text)
{
  (void)text;
  //static bool searchEngineEnabled=Config_getBool("SEARCHENGINE");
  //if (searchEngineEnabled)
  //{
  //  Doxygen::searchIndex->addWord(text,FALSE);
  //}
}


static ClassDef *stripClassName(const char *s)
{
  int pos=0;
  QCString type = s;
  QCString className;
  QCString templSpec;
  while (extractClassNameFromType(type,pos,className,templSpec)!=-1)
  {
    QCString clName=className+templSpec;

    ClassDef *cd=0;
    if (!g_classScope.isEmpty())
    {
      cd=getResolvedClass(g_currentDefinition,g_sourceFileDef,g_classScope+"::"+clName);
    }
    if (cd==0)
    {
      cd=getResolvedClass(g_currentDefinition,g_sourceFileDef,clName);
    }
    if (cd)
    {
      return cd;
    }
  }

  return 0;
}


/*! start a new line of code, inserting a line number if g_sourceFileDef
 * is TRUE. If a definition starts at the current line, then the line
 * number is linked to the documentation of that definition.
 */
static void startCodeLine()
{
  //if (g_currentFontClass) { g_code->endFontClass(); }
  if (g_sourceFileDef)
  {
    //QCString lineNumber,lineAnchor;
    //lineNumber.sprintf("%05d",g_yyLineNr);
    //lineAnchor.sprintf("l%05d",g_yyLineNr);
   
    Definition *d   = g_sourceFileDef->getSourceDefinition(g_yyLineNr);
    //printf("startCodeLine %d d=%p\n",g_yyLineNr,d);
    //g_code->startLineNumber();
    if (!g_includeCodeFragment && d && d->isLinkableInProject())
    {
      g_currentDefinition = d;
      g_currentMemberDef = g_sourceFileDef->getSourceMember(g_yyLineNr);
      g_insideBody = FALSE;
      g_searchingForBody = TRUE;
      g_realScope = d->name().copy();
      g_classScope = d->name().copy();
      //printf("Real scope: `%s'\n",g_realScope.data());
      g_bodyCurlyCount = 0;
      QCString lineAnchor;
      lineAnchor.sprintf("l%05d",g_yyLineNr);
      if (g_currentMemberDef)
      {
        g_code->writeLineNumber(g_currentMemberDef->getReference(),
	                        g_currentMemberDef->getOutputFileBase(),
	                        g_currentMemberDef->anchor(),g_yyLineNr);
        setCurrentDoc(
                                g_currentMemberDef->qualifiedName(),
	                        g_sourceFileDef->getSourceFileBase(),
	                        lineAnchor);
      }
      else
      {
        g_code->writeLineNumber(d->getReference(),
	                        d->getOutputFileBase(),
	                        0,g_yyLineNr);
        setCurrentDoc(
                                d->qualifiedName(),
	                        g_sourceFileDef->getSourceFileBase(),
	                        lineAnchor);
      }
    }
    else
    {
      //g_code->codify(lineNumber);
      g_code->writeLineNumber(0,0,0,g_yyLineNr);
    }
    //g_code->endLineNumber();
  }
  g_code->startCodeLine(); 
  if (g_currentFontClass)
  {
    g_code->startFontClass(g_currentFontClass);
  }
}

static void codify(const char* text) 
{ 
  g_code->codify(text);
}

static void endCodeLine()
{
  if (g_currentFontClass) { g_code->endFontClass(); }
  g_code->endCodeLine();
}

/*! writes a link to a fragment \a text that may span multiple lines, inserting
 * line numbers for each line. If \a text contains newlines, the link will be 
 * split into multiple links with the same destination, one for each line.
 */
static void writeMultiLineCodeLink(CodeOutputInterface &ol,
                  const char *ref,const char *file,
                  const char *anchor,const char *text,
                  const char *tooltip)
{
  bool done=FALSE;
  char *p=(char *)text;
  while (!done)
  {
    char *sp=p;
    char c;
    while ((c=*p++) && c!='\n') { }
    if (c=='\n')
    {
      g_yyLineNr++;
      *(p-1)='\0';
      //printf("writeCodeLink(%s,%s,%s,%s)\n",ref,file,anchor,sp);
      ol.writeCodeLink(ref,file,anchor,sp,tooltip);
      endCodeLine();
      if (g_yyLineNr<g_inputLines) 
      {
	startCodeLine();
      }
    }
    else
    {
      //printf("writeCodeLink(%s,%s,%s,%s)\n",ref,file,anchor,sp);
      ol.writeCodeLink(ref,file,anchor,sp,tooltip);
      done=TRUE;
    }
  }
}


static void codifyLines(char *text)
{
  //printf("codifyLines(%d,\"%s\")\n",g_yyLineNr,text);
  char *p=text,*sp=p;
  char c;
  bool done=FALSE;
  while (!done)
  {
    sp=p;
    while ((c=*p++) && c!='\n') { }
    if (c=='\n')
    {
      g_yyLineNr++;
      *(p-1)='\0';
      g_code->codify(sp);
      endCodeLine();
      if (g_yyLineNr<g_inputLines) 
      {
        // Re-enable sometime
	startCodeLine();
      }
    }
    else
    {
      g_code->codify(sp);
      done=TRUE;
    }
  }
}

static void addDocCrossReference(MemberDef *src,MemberDef *dst)
{
  if (dst->isTypedef() || dst->isEnumerate()) return; // don't add types
  //printf("addDocCrossReference src=%s,dst=%s\n",src->name().data(),dst->name().data());
  if ((Config_getBool("REFERENCED_BY_RELATION") || Config_getBool("CALLER_GRAPH")) && 
      (src->isFunction() || src->isSlot()) 
     )
  {
    dst->addSourceReferencedBy(src);
  }
  if ((Config_getBool("REFERENCES_RELATION") || Config_getBool("CALL_GRAPH")) && 
      (src->isFunction() || src->isSlot())
     )
  {
    src->addSourceReferences(dst);
  }

}



static bool getLinkInScope(const QCString &c,  // scope
                           const QCString &m,  // member
			   const char *memberText, // exact text
			   CodeOutputInterface &ol,
			   const char *text
			  )
{
  MemberDef    *md;
  ClassDef     *cd;
  FileDef      *fd;
  NamespaceDef *nd;
  GroupDef     *gd;
  //printf("Trying `%s'::`%s'\n",c.data(),m.data());
  if (getDefs(c,m,"()",md,cd,fd,nd,gd,FALSE,g_sourceFileDef) && 
      md->isLinkable())
  {
    //printf("Found!\n");
    //Definition *d=0;
    //if (cd) d=cd; else if (nd) d=nd; else if (fd) d=fd; else d=gd;

    Definition *d = md->getOuterScope()==Doxygen::globalScope ?
	            md->getBodyDef() : md->getOuterScope();
    if (md->getGroupDef()) d = md->getGroupDef();
    if (d && d->isLinkable())
    {
      g_theCallContext.setClass(stripClassName(md->typeString()));
      //printf("g_currentDefinition=%p g_currentMemberDef=%p g_insideBody=%d\n",
      //        g_currentDefinition,g_currentMemberDef,g_insideBody);

      if (g_currentDefinition && g_currentMemberDef &&
	  md!=g_currentMemberDef && g_insideBody)
      {
	addDocCrossReference(g_currentMemberDef,md);
      }
      //printf("d->getReference()=`%s' d->getOutputBase()=`%s' name=`%s' member name=`%s'\n",d->getReference().data(),d->getOutputFileBase().data(),d->name().data(),md->name().data());
     
      writeMultiLineCodeLink(ol,md->getReference(),
	                        md->getOutputFileBase(),
	                        md->anchor(),
				text ? text : memberText,
                                md->briefDescriptionAsTooltip());
      addToSearchIndex(text ? text : memberText);
      return TRUE;
    } 
  }
  return FALSE;
}

static bool getLink(const char *className,
                    const char *memberName,
		    CodeOutputInterface &ol,
		    const char *text=0)
{
  QCString m=removeRedundantWhiteSpace(memberName);
  QCString c=className;
  if (!getLinkInScope(c,m,memberName,ol,text))
  {
    if (!g_curClassName.isEmpty())
    {
      if (!c.isEmpty()) c.prepend("::");
      c.prepend(g_curClassName);
      return getLinkInScope(c,m,memberName,ol,text);
    }
    return FALSE;
  }
  return TRUE;
}


/*
  For a given string in the source code,
  finds its class or global id and links to it.

  As of June 1, '05, this ONLY finds classes
*/
static void generateClassOrGlobalLink(CodeOutputInterface &ol,char *clName,
                                      bool /*typeOnly*/=FALSE)
{
  QCString className=clName;

  // Don't do anything for empty text
  if (className.isEmpty()) return;

  Definition *cd=0; /// Class or namespace
  ClassDef *lcd=0;  /** Class def that we may find */
  MemberDef *md=0;        /** Member def that we may find */
  bool isLocal=FALSE;

  // printf("generateClassOrGlobalLink(className=%s)\n",className.data());

  if ((lcd=g_theVarContext.findVariable(className))==0) // not a local variable
  {
    Definition *d = g_currentDefinition;

    cd = getResolvedClass(d,g_sourceFileDef,className,&md);
    if(! cd) /// \todo: enhance namespace detection.
      cd = findNameSpace(className);

    //printf("d=%p g_sourceFileDef=%p\n",d,g_currentDefinition);
    //printf("is found as a type %s\n",cd?cd->name().data():"<null>");

    if (cd==0 && md==0) // also see if it is variable or enum or enum value
    {
      if (getLink(g_classScope,clName,ol,clName))
      {
	return;
      }
    }
  }
  else
  {
    if (lcd!=RubyVariableContext::dummyContext) 
    {
      g_theCallContext.setClass(lcd);
    }
    isLocal=TRUE;
    //fprintf(stderr,"is a local variable cd=%p!\n",cd);
  }

  if (cd && cd->isLinkable()) // is it a linkable class
  {
    writeMultiLineCodeLink(ol,cd->getReference(),cd->getOutputFileBase(),0,clName,cd->briefDescriptionAsTooltip());
    addToSearchIndex(className);
    if (md)
    {
      Definition *d = md->getOuterScope()==Doxygen::globalScope ?
                      md->getBodyDef() : md->getOuterScope();
      if (md->getGroupDef()) d = md->getGroupDef();
      if (d && d->isLinkable() && md->isLinkable() && g_currentMemberDef)
      {
        addDocCrossReference(g_currentMemberDef,md);
      }
    }
  }
  else // not a class, maybe a global member
  {

    /*
      This code requires a going-over in order to
      make it work for Python

    //printf("class %s not linkable! cd=%p md=%p typeOnly=%d\n",clName,cd,md,typeOnly);
    if (!isLocal && (md!=0 || (cd==0 && !typeOnly))) // not a class, see if it is a global enum/variable/typedef.
    {
      if (md==0) // not found as a typedef
      {
	md = setCallContextForVar(clName);
	//printf("setCallContextForVar(%s) md=%p g_currentDefinition=%p\n",clName,md,g_currentDefinition);
	if (md && g_currentDefinition)
	{
	  //fprintf(stderr,"%s accessible from %s? %d md->getOuterScope=%s\n",
	  //    md->name().data(),g_currentDefinition->name().data(),
	  //    isAccessibleFrom(g_currentDefinition,g_sourceFileDef,md),
	  //    md->getOuterScope()->name().data());
	}
	     
        if (md && g_currentDefinition && 
	    isAccessibleFrom(g_currentDefinition,g_sourceFileDef,md)==-1)
	{
	  md=0; // variable not accessible
	}
      }
      if (md)
      {
        //printf("is a global md=%p g_currentDefinition=%s\n",md,g_currentDefinition?g_currentDefinition->name().data():"<none>");
	if (md->isLinkable())
	{
	  writeMultiLineCodeLink(ol,md->getReference(),md->getOutputFileBase(),md->anchor(),clName,md->briefDescriptionAsTooltip());
          addToSearchIndex(clName);
	  if (g_currentMemberDef)
	  {
	    addDocCrossReference(g_currentMemberDef,md);
	  }
	  return;
	}
      }
    }

    */
    
    // nothing found, just write out the word
    codifyLines(clName);
    addToSearchIndex(clName);
  }
}

/*
   As of June 1, this function seems to work
   for file members, but scopes are not
   being correctly tracked for classes
   so it doesn't work for classes yet.

*/
static void generateFunctionLink(CodeOutputInterface &ol,char *funcName)
{
  //CodeClassDef *ccd=0;
  ClassDef *ccd=0;
  QCString locScope=g_classScope.copy();
  QCString locFunc=removeRedundantWhiteSpace(funcName);
  //fprintf(stdout,"*** locScope=%s locFunc=%s\n",locScope.data(),locFunc.data());
  int i=locFunc.findRev("::");
  if (i>0)
  {
    locScope=locFunc.left(i);
    locFunc=locFunc.right(locFunc.length()-i-2).stripWhiteSpace();
  }
  //printf("generateFunctionLink(%s) classScope=`%s'\n",locFunc.data(),locScope.data());
  if (!locScope.isEmpty() && (ccd=g_codeClassSDict[locScope]))
  {
    //printf("using classScope %s\n",g_classScope.data());
    if (ccd->baseClasses())
    {
      BaseClassListIterator bcli(*ccd->baseClasses());
      for ( ; bcli.current() ; ++bcli)
      {
	if (getLink(bcli.current()->classDef->name(),locFunc,ol,funcName)) 
	{
	  return;
	}
      }
    }
  }
  if (!getLink(locScope,locFunc,ol,funcName))
  {
    generateClassOrGlobalLink(ol,funcName);
  }
  return;
}

static bool findMemberLink(CodeOutputInterface &ol,Definition *sym,const char *symName)
{
  //printf("sym %s outerScope=%s equal=%d\n",
  //    sym->name().data(),sym->getOuterScope()->name().data(),
  //    sym->getOuterScope()==g_currentDefinition);

  if (sym->getOuterScope() &&
      sym->getOuterScope()->definitionType()==Definition::TypeClass &&
      g_currentDefinition->definitionType()==Definition::TypeClass)
  {
    ClassDef *cd = (ClassDef*)sym->getOuterScope();
    ClassDef *thisCd = (ClassDef *)g_currentDefinition;
    QCString anchor;
    if (sym->definitionType()==Definition::TypeMember)
    {
      anchor=((MemberDef *)sym)->anchor();
    }

    // TODO: find the nearest base class in case cd is a base class of
    // thisCd 
    if (cd==thisCd) 
    {
      writeMultiLineCodeLink(ol,sym->getReference(),
          sym->getOutputFileBase(),
          anchor,
          symName,
          sym->briefDescriptionAsTooltip());
      return TRUE;
    }
  }
  return FALSE;
}

static void findMemberLink(CodeOutputInterface &ol,char *symName)
{
  //printf("Member reference: %s scope=%s member=%s\n",
  //    yytext,
  //    g_currentDefinition?g_currentDefinition->name().data():"<none>",
  //    g_currentMemberDef?g_currentMemberDef->name().data():"<none>"
  //    );
  if (g_currentDefinition)
  {
    DefinitionIntf *di = Doxygen::symbolMap->find(symName);
    if (di)
    {
      if (di->definitionType()==DefinitionIntf::TypeSymbolList) // multiple symbols
      {
	DefinitionListIterator dli(*(DefinitionList*)di);
	Definition *sym;
	for (dli.toFirst();(sym=dli.current());++dli)
	{
	  if (findMemberLink(ol,sym,symName)) return;
	}
      }
      else // single symbol
      {
	if (findMemberLink(ol,(Definition*)di,symName)) return;
      }
    }
  }
  //printf("sym %s not found\n",&yytext[5]);
  codify(symName);
}

static void startFontClass(const char *s)
{
  endFontClass();
  g_code->startFontClass(s);
  g_currentFontClass=s;
}

static void endFontClass()
{
  if (g_currentFontClass)
  {
    g_code->endFontClass();
    g_currentFontClass=0;
  }
}

/// A very handy shortcut...
static void codify(const char* text, const char * fontclass) 
{ 
  startFontClass(fontclass);
  g_code->codify(text);
  endFontClass();
}

#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) result=yyread(buf,max_size);

static int yyread(char *buf,int max_size)
{
  int c=0;
  while( c < max_size && g_inputString[g_inputPosition] )
  {
    *buf = g_inputString[g_inputPosition++] ;
    c++; buf++;
  }
  return c;
}

%}


BB                [ \t]+
B                 [ \t]*
NEWLINE           \n

DIGIT             [0-9]
LETTER            [A-Za-z]
NONEMPTY          [A-Za-z0-9_]
EXPCHAR           [#(){}\[\],:.%/\\=`*~|&<>!;+-]
NONEMPTYEXP       [^ \t\n:]
PARAMNONEMPTY     [^ \t\n():]
IDENTIFIER        ({LETTER}|"_")({LETTER}|{DIGIT}|"_")*  
BORDER            ([^A-Za-z0-9])

POUNDCOMMENT      "#".*

TRISINGLEQUOTE    "'''"
TRIDOUBLEQUOTE    "\"\"\""
LONGSTRINGCHAR    [^\\"']
ESCAPESEQ         ("\\")(.)
LONGSTRINGITEM    ({LONGSTRINGCHAR}|{ESCAPESEQ})
SMALLQUOTE        ("\"\""|"\""|"'"|"''")
LONGSTRINGBLOCK   ({LONGSTRINGITEM}+|{SMALLQUOTE})

SHORTSTRING       ("'"{SHORTSTRINGITEM}*"'"|'"'{SHORTSTRINGITEM}*'"')
SHORTSTRINGITEM   ({SHORTSTRINGCHAR}|{ESCAPESEQ})
SHORTSTRINGCHAR   [^\\\n"]
STRINGLITERAL     {STRINGPREFIX}?( {SHORTSTRING} | {LONGSTRING})  
STRINGPREFIX      ("r"|"u"|"ur"|"R"|"U"|"UR"|"Ur"|"uR")
QUOTES            ("\""[^"]*"\"")
SINGLEQUOTES      ("'"[^']*"'")

LONGINTEGER       {INTEGER}("l"|"L")
INTEGER           ({DECIMALINTEGER}|{OCTINTEGER}|{HEXINTEGER})
DECIMALINTEGER    ({NONZERODIGIT}{DIGIT}*|"0")
OCTINTEGER        "0"{OCTDIGIT}+
HEXINTEGER        "0"("x"|"X"){HEXDIGIT}+  
NONZERODIGIT      [1-9]  
OCTDIGIT          [0-7]  
HEXDIGIT          ({DIGIT}|[a-f]|[A-F])
FLOATNUMBER       ({POINTFLOAT}|{EXPONENTFLOAT})
POINTFLOAT        ({INTPART}?{FRACTION}|{INTPART}".")  
EXPONENTFLOAT     ({INTPART}|{POINTFLOAT}){EXPONENT}
INTPART             {DIGIT}+  
FRACTION             "."{DIGIT}+  
EXPONENT             ("e"|"E")("+"|"-")?{DIGIT}+
IMAGNUMBER ({FLOATNUMBER}|{INTPART})("j"|"J")
ATOM              ({IDENTIFIER}|{LITERAL}|{ENCLOSURE})
ENCLOSURE             ({PARENTH_FORM}|{LIST_DISPLAY}|{DICT_DISPLAY}|{STRING_CONVERSION})
LITERAL             ({STRINGLITERAL}|{INTEGER}|{LONGINTEGER}|{FLOATNUMBER}|{IMAGNUMBER})
PARENTH_FORM       "("{EXPRESSION_LIST}?")"
TEST             ({AND_TEST}("or"{AND_TEST})*|{LAMBDA_FORM})
TESTLIST             {TEST}( ","{TEST})*","?
LIST_DISPLAY        "["{LISTMAKER}?"]"  
LISTMAKER             {EXPRESSION}({LIST_FOR}|(","{EXPRESSION})*","?)  
LIST_ITER             ({LIST_FOR}|{LIST_IF})  
LIST_FOR             "for"{EXPRESSION_LIST}"in"{TESTLIST}{LIST_ITER}?
LIST_IF             "if"{TEST}{LIST_ITER}?
DICT_DISPLAY             "\{"{KEY_DATUM_LIST}?"\}"
KEY_DATUM_LIST       {KEY_DATUM}(","{KEY_DATUM})*","? 
KEY_DATUM              {EXPRESSION}":"{EXPRESSION}
STRING_CONVERSION        "`"{EXPRESSION_LIST}"`"
PRIMARY             ({ATOM}|{ATTRIBUTEREF}|{SUBSCRIPTION}|{SLICING}|{CALL})
ATTRIBUTEREF             {PRIMARY}"."{IDENTIFIER}
SUBSCRIPTION             {PRIMARY}"["{EXPRESSION_LIST}"]"
SLICING            ({SIMPLE_SLICING}|{EXTENDED_SLICING})
SIMPLE_SLICING             {PRIMARY}"["{SHORT_SLICE}"]"  
EXTENDED_SLICING           {PRIMARY}"["{SLICE_LIST}"]" 
SLICE_LIST          {SLICE_ITEM}(","{SLICE_ITEM})*","?
SLICE_ITEM           ({EXPRESSION}|{PROPER_SLICE}|{ELLIPSIS})
PROPER_SLICE           ({SHORT_SLICE}|{LONG_SLICE})
SHORT_SLICE              {LOWER_BOUND}?":"{UPPER_BOUND}?  
LONG_SLICE             {SHORT_SLICE}":"{STRIDE}?
LOWER_BOUND             {EXPRESSION}  
UPPER_BOUND             {EXPRESSION}
STRIDE             {EXPRESSION}
ELLIPSIS             "..."
CALL             {PRIMARY}"("({ARGUMENT_LIST}","?)?")"
ARGUMENT_LIST       ({POSITIONAL_ARGUMENTS}(","{KEYWORD_ARGUMENTS})?(",""*"{EXPRESSION})?(",""**"{EXPRESSION})?|{KEYWORD_ARGUMENTS}(",""*"{EXPRESSION})?(",""**"{EXPRESSION})?|"*"{EXPRESSION}(",""**"{EXPRESSION})?|"**"{EXPRESSION})
POSITIONAL_ARGUMENTS             {EXPRESSION}(","{EXPRESSION})*
KEYWORD_ARGUMENTS              {KEYWORD_ITEM}(","{KEYWORD_ITEM})*
KEYWORD_ITEM           {IDENTIFIER}"="{EXPRESSION}
POWER             {PRIMARY}("**"{U_EXPR})?
U_EXPR            ({POWER}|"-"{U_EXPR}|"+"{U_EXPR}|"\~"{U_EXPR})
M_EXPR            ({U_EXPR}|{M_EXPR}"*"{U_EXPR}|{M_EXPR}"//"{U_EXPR}|{M_EXPR}"/"{U_EXPR}|{M_EXPR}"\%"{U_EXPR})
A_EXPR         ({M_EXPR}|{A_EXPR}"+"{M_EXPR}|{A_EXPR}"-"{M_EXPR}
SHIFT_EXPR            ({A_EXPR}|{SHIFT_EXPR}("<<"|">>"){A_EXPR})
AND_EXPR            ({SHIFT_EXPR}|{AND_EXPR}"\;SPMamp;"{SHIFT_EXPR}
XOR_EXPR            ({AND_EXPR}|{XOR_EXPR}"\textasciicircum"{AND_EXPR})
OR_EXPR            ({XOR_EXPR}|{OR_EXPR}"|"{ XOR_EXPR})

COMPARISON             {OR_EXPR}({COMP_OPERATOR}{OR_EXPR})*
COMP_OPERATOR         ("<"|">"|"=="|">="|"<="|"<>"|"!="|"is""not"?|"not"?"in")
EXPRESSION            ({OR_TEST}|{LAMBDA_FORM})
OR_TEST             ({AND_TEST}|{OR_TEST}"or"{AND_TEST})
AND_TEST          ({NOT_TEST}|{AND_TEST}"and"{NOT_TEST})
NOT_TEST           ({COMPARISON}|"not"{NOT_TEST})
LAMBDA_FORM       "lambda"{PARAMETER_LIST}?":"{EXPRESSION}
EXPRESSION_LIST      {EXPRESSION}(","{EXPRESSION})*","?
SIMPLE_STMT       ({EXPRESSION_STMT}|{ASSERT_STMT}|{ASSIGNMENT_STMT}|{AUGMENTED_ASSIGNMENT_STMT}|{PASS_STMT}|{DEL_STMT}|{PRINT_STMT}|{RETURN_STMT}|{YIELD_STMT}|{RAISE_STMT}|{BREAK_STMT}|{CONTINUE_STMT}|{IMPORT_STMT}|{GLOBAL_STMT}|{EXEC_STMT})
EXPRESSION_STMT     {EXPRESSION_LIST}
ASSERT_STMT             "assert"{EXPRESSION}(","{EXPRESSION})?
ASSIGNMENT_STMT     ({TARGET_LIST}"=")+{EXPRESSION_LIST}
TARGET_LIST             {TARGET}(","{TARGET})*","?
TARGET           ({IDENTIFIER}|"("{TARGET_LIST}")"|"["{TARGET_LIST}"]"|{ATTRIBUTEREF}|{SUBSCRIPTION}|{SLICING})

      /* limit of a word */
WLIM   	  	  [^[:alnum:]!?_]
CAPITAL           [A-Z]
CONSTNAME         {CAPITAL}({LETTER}|{DIGIT}|"_")*
FUNCNAME          {IDENTIFIER}([?!]|{B}=)?

      /* Expressions starting a block that must finish with and end */
      /* the ones that must start with a statement */
SBLOCK	     	  if|while|until|unless
      /* the ones for which we don't care too much */
EBLOCK	     	  begin|proc|do|for|def|case|module|class({B}<<)?

      /* keywords...*/
KEYWORDS          or|and|not|for|in|if|try|yield|raise|break|continue|return|while|elsif|else|rescue|throw|when

      /* special values */

SPECIAL		  true|false|nil|self
HEREDOC           <<-?['"]?({LETTER}|{DIGIT}|"_")+['"]?


%option noyywrap
%option nounput
  
  /** \todo copy from the scanner -> ?*/

  /** \todo Various things:
    * the most important is probably the constants definition
  */

  /* used for global or class-like scopes */
%x Outer

  /* used for inner scopes (function definitions, loops...) */
%x Inner


%x FunctionDec
%x FunctionParams

%x ClassDec
%x ClassInheritance

  /* string states */
%x SingleQuotedString
%x DoubleQuotedString
%x HereDoc
%x Regexp

%%

<Outer,Inner>{
  {HEREDOC} 	      {
  		        if(1) { 
			  hereDocContext = HereDoc;
			  QCString str = yytext;
			  str.stripPrefix("<<");
			  str = str.stripWhiteSpace();
			  str.stripPrefix("-");
			  str.stripPrefix("'");
			  str.stripPrefix("\"");
			  if(str.contains('\'') || str.contains('"'))
			    str = str.left(str.size() - 2);
			  g_heredoc_marker = str.stripWhiteSpace();
			  g_pending_heredoc = TRUE;
			  // printf("Found pending here document: %s\n",
			  // 	 (const char*) g_heredoc_marker);
			}
			codify(yytext, "stringliteral");
			bookKeeping();
			// it will only trigger at end of line...
  		      }

  "'"		      {
  		        PUSH_SC(SingleQuotedString);
			startFontClass("stringliteral");
			codify(yytext);
			bookKeeping();
		      }

  \" 		      {
  		        PUSH_SC(DoubleQuotedString);
			startFontClass("stringliteral");
			codify(yytext);
			bookKeeping();
		      }

  "/"		      {
  		        if(context.surelyExpression) {
  		          PUSH_SC(Regexp);
			  codify(yytext, "stringliteral");
			}
			else
			  codify(yytext);
			bookKeeping();
		      }

}


<Outer>{
  "def"{BB}             {
  			  /// \todo add parsing for various things, such as
			  /// attributes, constants, funcalls...
  			  if(context.definitionOK) {
			    codify(yytext, "keyword");
			    BEGIN( FunctionDec );
			  }
			  else
			    codify(yytext);
			  bookKeeping();
		        }

  (class|module)/{WLIM} { // class definition
  			  if(context.definitionOK) {
			    codify(yytext, "keyword");
			    BEGIN( ClassDec );
			  }
			  else
			    codify(yytext);
			  bookKeeping();
		        }

}


  /* When in this state, we ignore everything until the matching end */
<Inner>{
  "end"/{WLIM}        {	
  		        if(context.definitionOK) {
			  POP_SC;
			  codify(yytext, "keyword");
			}
			else
			  codify(yytext);
			bookKeeping();
		      }

}

<Outer,Inner>{
  {EBLOCK}/{WLIM}    {
  			if(context.expressionOK) {
			  PUSH_SC(Inner);
			  codify(yytext, "keyword");
                        }
			else
			  codify(yytext);
			bookKeeping();
		      }

  {SBLOCK}/{WLIM}    {
  			if(context.ifNewBlock) {
			  PUSH_SC(Inner);
			  codify(yytext, "keyword");
                        }
			else if(context.expressionOK) {
			  codify(yytext, "keyword");
                        }
			else
			  codify(yytext);
			bookKeeping();
		      }

  {KEYWORDS}/{WLIM}   {
  		        if(context.expressionOK)
  		          codify(yytext, "keyword");
			else
			  codify(yytext);
			bookKeeping();
		      }

  {SPECIAL}/{WLIM}   {
  		        if(context.expressionOK)
  		          codify(yytext, "keywordflow"); // looks pretty nice
			else
			  codify(yytext);
			bookKeeping();
		      }

  {POUNDCOMMENT}      {
			codify(yytext, "comment");
			bookKeeping();
                      }

  {NEWLINE}           {
  		        bookKeeping();
  		        codifyLines(yytext);
  		      }

  .                   { 
  		        // printf("Slurping: '%s'\n", yytext);
			codify(yytext);
  		        bookKeeping();
                      }
}



<ClassDec>{
  
  {CONSTNAME}         {
			generateClassOrGlobalLink(*g_code,yytext);
			// codify(yytext);
			g_curClassName = yytext;
                        enterScope(yytext);
			g_curClassBases.clear();
			BEGIN( ClassInheritance );
 			bookKeeping();
		      }

  .                   {
  		        codify(yytext);
  		        bookKeeping();
		      }
}

<ClassInheritance>{
   {CONSTNAME}        {
   		        g_curClassBases.inSort(yytext);
			generateClassOrGlobalLink(*g_code,yytext);
  		        bookKeeping();
		      }
		      
   [\n;]              {
  		        bookKeeping();
			codifyLines(yytext);
			BEGIN(Outer);
		      }

   .	              {
		        codify(yytext);
			BEGIN(Outer);
  		        bookKeeping();
		      }

}


<FunctionDec>{

  {CONSTNAME}         {
			generateClassOrGlobalLink(*g_code,yytext);
			// codify(yytext);
			g_curClassName = yytext;
                        enterScope(yytext);
			g_curClassBases.clear();
			BEGIN( ClassInheritance );
 			bookKeeping();
		      }

  "self"	      {
  		        codify(yytext, "keywordflow");
			bookKeeping();
  		      }

   {FUNCNAME}         {
                        generateFunctionLink(*g_code,yytext);
  		        bookKeeping();
                      }

   {B}"("             {
		        codify(yytext);
		  	BEGIN( FunctionParams );
  		        bookKeeping();
		      }

   [;\n]	      {
  		        bookKeeping();
   		        codifyLines(yytext);
			BEGIN(Outer);
			PUSH_SC(Inner);
                      }

   .                  {
		        codify(yytext);
  		        bookKeeping();
		      }


}

<FunctionParams>{
    ({BB}|",")        {
                        // Parses delimiters
			codify(yytext);
  		        bookKeeping();
                      }

    ({IDENTIFIER}|{PARAMNONEMPTY}+) {
				      codify(yytext);
  		        	      bookKeeping();
                                    }

    {NEWLINE}         {
                        codifyLines(yytext);
		      }

    ")"               {
                        codify(yytext);
  		        bookKeeping();
			BEGIN(Outer);
			PUSH_SC(Inner);
                      }
}

<SingleQuotedString>{

  "'"		      {
			codify(yytext);
			if(! context.pendingBackspace) {
  		          POP_SC;
			  endFontClass();
			}
			bookKeeping();
		      }

  [^']	       	      {
			bookKeeping();
			codifyLines(yytext);
		      }


}

<Regexp>{

  "/"		      {
			codify(yytext);
			if(! context.pendingBackspace) {
  		          POP_SC;
			  endFontClass();
			}
			bookKeeping();
		      }

  [^/]		      {
			bookKeeping();
			codifyLines(yytext);
		      }
}


  /* Todo: this should be handling as well the #{ ... } 
     substitution that can contain arbitraty code, such as
     "end", for instance.
  */

<DoubleQuotedString>{

  \"		      {
			codify(yytext);
			if(! context.pendingBackspace) {
  		          POP_SC;
			  endFontClass();
			}
			bookKeeping();
  		      }

  [^"]		      {
			bookKeeping();
			codifyLines(yytext);
		      }

}
<HereDoc>{
  .* 	              {
 		        QCString line = QCString(yytext).stripWhiteSpace();
 			if(g_heredoc_marker == line) {
			  POP_SC;
			  endFontClass();
                        }
			codify(yytext);
 			bookKeeping();
 		      }
  {NEWLINE}           { // so that newlines are not taken into account.
 			bookKeeping();
			codifyLines(yytext);
		      }
}


%%

/*@ ----------------------------------------------------------------------------
 */

void resetRubyCodeParserState() 
{
  g_currentDefinition = 0;
  g_currentMemberDef = 0;
  g_doubleStringIsDoc = FALSE;
  g_paramParens = 0;
  g_indents.clear();
  BEGIN( Outer );
}

void parseRubyCode(CodeOutputInterface &od,const char *className,
                 const QCString &s,bool exBlock, const char *exName,
		 FileDef *fd,int startLine,int endLine,bool inlineFragment,
		 MemberDef *) 
{

  //printf("***parseCode()\n");
  
  //--- some code to eliminate warnings---
  className = "";
  exBlock = FALSE;
  exName = "";
  inlineFragment = "";
  //--------------------------------------
  if (s.isEmpty()) return;
  g_code = &od;
  g_inputString   = s;
  g_inputPosition = 0;
  g_currentFontClass = 0;
  g_needsTermination = FALSE;

  // needs to be initialize here
  hereDocContext = HereDoc;
  if (endLine!=-1)
    g_inputLines  = endLine+1;
  else
    g_inputLines  = countLines();
  
  if (startLine!=-1)
    g_yyLineNr    = startLine;
  else
    g_yyLineNr    = 1;
  
  g_exampleBlock  = exBlock; 
  g_exampleName   = exName;
  g_sourceFileDef = fd;


  // Starts line 1 on the output  
  startCodeLine();

  context.reset();
  rubycodeYYrestart( rubycodeYYin );

  rubycodeYYlex();

  if (!g_indents.isEmpty()) 
  {
    // printf("Exited pysourceparser in inconsistent state!\n");
  }

  if (g_needsTermination)
  {
    endFontClass();
    g_code->endCodeLine();
  }
  return;
}


#if !defined(YY_FLEX_SUBMINOR_VERSION) 
extern "C" { // some bogus code to keep the compiler happy
  void rubycodeYYdummy() { yy_flex_realloc(0,0); } 
}
#elif YY_FLEX_SUBMINOR_VERSION<33
#error "You seem to be using a version of flex newer than 2.5.4. These are currently incompatible with 2.5.4, and do NOT work with doxygen! Please use version 2.5.4 or expect things to be parsed wrongly! A bug report has been submitted (#732132)."
#endif

