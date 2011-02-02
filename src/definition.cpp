/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2011 by Dimitri van Heesch.
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

#include "qtbc.h"
#include <ctype.h>
#include <qregexp.h>
#include <md5.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "config.h"
#include "definition.h"
#include "doxygen.h"
#include "language.h"
#include "message.h"
#include "outputlist.h"
#include "code.h"
#include "util.h"
#include "groupdef.h"
#include "pagedef.h"
#include "section.h"
#include "htags.h"
#include "parserintf.h"
#include "marshal.h"
#include "debug.h"

#define START_MARKER 0x4445465B // DEF[
#define END_MARKER   0x4445465D // DEF]

//-----------------------------------------------------------------------------------------

class DefinitionImpl
{
  public:
    DefinitionImpl();
   ~DefinitionImpl();
    void init(const char *df,int dl,
         const char *n);

    SectionDict *sectionDict;  // dictionary of all sections, not accessible

    MemberSDict *sourceRefByDict;       
    MemberSDict *sourceRefsDict;        
    QList<ListItemInfo> *xrefListItems; 
    GroupList *partOfGroups;            

    DocInfo   *details;    // not exported
    DocInfo   *inbodyDocs; // not exported
    BriefInfo *brief;      // not exported
    BodyInfo  *body;       // not exported
    QCString   docSignatures;

    QCString localName;      // local (unqualified) name of the definition
                             // in the future m_name should become m_localName
    QCString qualifiedName;
    QCString ref;   // reference to external documentation

    bool hidden;
    bool isArtificial;

    Definition *outerScope;  // not owner

    // where the item was found
    QCString defFileName;
    int      defLine;
    QCString defFileExt;
};

DefinitionImpl::DefinitionImpl() 
  : sectionDict(0), sourceRefByDict(0), sourceRefsDict(0), 
    xrefListItems(0), partOfGroups(0),
    details(0), inbodyDocs(0), brief(0), body(0), 
    outerScope(0)
{
}

DefinitionImpl::~DefinitionImpl()
{
  delete sectionDict;
  delete sourceRefByDict;
  delete sourceRefsDict;
  delete partOfGroups;
  delete xrefListItems;
  delete brief;
  delete details;
  delete body;
  delete inbodyDocs;
}

void DefinitionImpl::init(const char *df,int dl,
                          const char *n)
{
  defFileName = df;
  int lastDot = defFileName.findRev('.');
  if (lastDot!=-1)
  {
    defFileExt = defFileName.mid(lastDot);
  }
  defLine = dl;
  QCString name = n;
  if (name!="<globalScope>") 
  {
    //extractNamespaceName(m_name,m_localName,ns);
    localName=stripScope(n);
  }
  else
  {
    localName=n;
  }
  //printf("m_localName=%s\n",m_localName.data());

  brief           = 0;
  details         = 0;
  body            = 0;
  inbodyDocs      = 0;
  sourceRefByDict = 0;
  sourceRefsDict  = 0;
  sectionDict     = 0, 
  outerScope      = Doxygen::globalScope;
  partOfGroups    = 0;
  xrefListItems   = 0;
  hidden          = FALSE;
  isArtificial    = FALSE;
}

//-----------------------------------------------------------------------------------------

static bool matchExcludedSymbols(const char *name)
{
  static QStrList &exclSyms = Config_getList("EXCLUDE_SYMBOLS");
  if (exclSyms.count()==0) return FALSE; // nothing specified
  const char *pat = exclSyms.first();
  QCString symName = name;
  while (pat)
  {
    QCString pattern = pat;
    bool forceStart=FALSE;
    bool forceEnd=FALSE;
    if (pattern.at(0)=='^') 
      pattern=pattern.mid(1),forceStart=TRUE;
    if (pattern.at(pattern.length()-1)=='$') 
      pattern=pattern.left(pattern.length()-1),forceEnd=TRUE;
    if (pattern.find('*')!=-1) // wildcard mode
    {
      QRegExp re(substitute(pattern,"*",".*"),TRUE);
      int i,pl;
      i = re.match(symName,0,&pl);
      //printf("  %d = re.match(%s) pattern=%s\n",i,symName.data(),pattern.data());
      if (i!=-1) // wildcard match
      {
        int sl=symName.length();
        // check if it is a whole word match
        if ((i==0     || pattern.at(0)=='*'    || (!isId(symName.at(i-1))  && !forceStart)) &&
            (i+pl==sl || pattern.at(i+pl)=='*' || (!isId(symName.at(i+pl)) && !forceEnd))
           )
        {
          //printf("--> name=%s pattern=%s match at %d\n",symName.data(),pattern.data(),i);
          return TRUE;
        }
      }
    }
    else if (!pattern.isEmpty()) // match words
    {
      int i = symName.find(pattern);
      if (i!=-1) // we have a match!
      {
        int pl=pattern.length();
        int sl=symName.length();
        // check if it is a whole word match
        if ((i==0     || (!isId(symName.at(i-1))  && !forceStart)) &&
            (i+pl==sl || (!isId(symName.at(i+pl)) && !forceEnd))
           )
        {
          //printf("--> name=%s pattern=%s match at %d\n",symName.data(),pattern.data(),i);
          return TRUE; 
        }
      }
    }
    pat = exclSyms.next();
  }
  //printf("--> name=%s: no match\n",name);
  return FALSE;
}

void Definition::addToMap(const char *name,Definition *d)
{
  bool vhdlOpt = Config_getBool("OPTIMIZE_OUTPUT_VHDL");
  QCString symbolName = name;
  int index=computeQualifiedIndex(symbolName);
  if (!vhdlOpt && index!=-1) symbolName=symbolName.mid(index+2);
  if (!symbolName.isEmpty()) 
  {
    //printf("******* adding symbol `%s' (%p)\n",symbolName.data(),d);
    DefinitionIntf *di=Doxygen::symbolMap->find(symbolName);
    //printf("  addToMap(%p): looking for symbol %s: %p\n",d,symbolName.data(),di);
    if (di==0) // new Symbol
    {
      //printf("  new symbol!\n");
      Doxygen::symbolMap->insert(symbolName,d);
    }
    else // existing symbol
    {
      //printf("  existing symbol: ");
      if (di->definitionType()==DefinitionIntf::TypeSymbolList) // already multiple symbols
      {
        //printf("adding to exiting list\n");
        DefinitionList *dl = (DefinitionList*)di;
        dl->append(d);
      }
      else // going from one to two symbols
      {
        Doxygen::symbolMap->take(symbolName);
        DefinitionList *dl = new DefinitionList;
        //printf("replacing symbol by list %p with elements %p and %p\n",dl,di,d);
        dl->append((Definition*)di);
        dl->append(d);
        Doxygen::symbolMap->insert(symbolName,dl);
      }
    }

    // auto resize if needed
    static int sizeIndex=9;
    if (Doxygen::symbolMap->size()>SDict_primes[sizeIndex])
    {
      Doxygen::symbolMap->resize(SDict_primes[++sizeIndex]);
    }

    d->_setSymbolName(symbolName);
  }
}

void Definition::removeFromMap(Definition *d)
{
  QString symbolName = d->m_symbolName;
  if (!symbolName.isEmpty()) 
  {
    //printf("******* removing symbol `%s' (%p)\n",symbolName.data(),d);
    DefinitionIntf *di=Doxygen::symbolMap->find(symbolName);
    if (di)
    {
      if (di!=d) // symbolName not unique
      {
        //printf("  removing from list: %p!\n",di);
        DefinitionList *dl = (DefinitionList*)di;
        bool b = dl->removeRef(d);
        ASSERT(b==TRUE);
        if (dl->isEmpty())
        {
          Doxygen::symbolMap->take(symbolName);
        }
      }
      else // symbolName unique
      {
        //printf("  removing symbol %p\n",di);
        Doxygen::symbolMap->take(symbolName);
      }
    }
  }
}

Definition::Definition(const char *df,int dl,
                       const char *name,const char *b,
                       const char *d,bool isSymbol)
{
  m_name = name;
  m_impl = new DefinitionImpl;
  m_impl->init(df,dl,name);
  m_isSymbol = isSymbol;
  if (isSymbol) addToMap(name,this);
  _setBriefDescription(b,df,dl);
  _setDocumentation(d,df,dl,TRUE,FALSE);
  if (matchExcludedSymbols(name)) 
  {
    m_impl->hidden = TRUE;
  }
}

Definition::~Definition()
{
  if (m_isSymbol) 
  {
    removeFromMap(this);
  }
  if (m_impl)
  {
    delete m_impl;
    m_impl=0;
  }
}

void Definition::setName(const char *name)
{
  if (name==0) return;
  m_name = name;
}

void Definition::addSectionsToDefinition(QList<SectionInfo> *anchorList)
{
  if (!anchorList) return;
  makeResident();
  //printf("%s: addSectionsToDefinition(%d)\n",name().data(),anchorList->count());
  SectionInfo *si=anchorList->first();
  while (si)
  {
    //printf("Add section `%s' to definition `%s'\n",
    //    si->label.data(),name().data());
    SectionInfo *gsi=Doxygen::sectionDict.find(si->label);
    if (gsi==0)
    {
      gsi = new SectionInfo(*si);
      Doxygen::sectionDict.insert(si->label,gsi);
    }
    if (m_impl->sectionDict==0) 
    {
      m_impl->sectionDict = new SectionDict(17);
    }
    if (m_impl->sectionDict->find(gsi->label)==0)
    {
      m_impl->sectionDict->insert(gsi->label,gsi);
      gsi->definition = this;
    }
    si=anchorList->next();
  }
}

void Definition::writeDocAnchorsToTagFile()
{
  makeResident();
  if (!Config_getString("GENERATE_TAGFILE").isEmpty() && m_impl->sectionDict)
  {
    //printf("%s: writeDocAnchorsToTagFile(%d)\n",name().data(),m_sectionDict->count());
    QDictIterator<SectionInfo> sdi(*m_impl->sectionDict);
    SectionInfo *si;
    for (;(si=sdi.current());++sdi)
    {
      if (!si->generated)
      {
        //printf("write an entry!\n");
        if (definitionType()==TypeMember) Doxygen::tagFile << "  ";
        Doxygen::tagFile << "    <docanchor file=\"" 
                         << si->fileName << "\">" << si->label 
                         << "</docanchor>" << endl;
      }
    }
  }
}

bool Definition::_docsAlreadyAdded(const QCString &doc)
{
  uchar md5_sig[16];
  QCString sigStr(33);
  // to avoid mismatches due to differences in indenting, we first remove
  // double whitespaces...
  QCString docStr = doc.simplifyWhiteSpace();
  MD5Buffer((const unsigned char *)docStr.data(),docStr.length(),md5_sig);
  MD5SigToString(md5_sig,sigStr.data(),33);
  if (m_impl->docSignatures.find(sigStr)==-1) // new docs, add signature to prevent re-adding it
  {
    m_impl->docSignatures+=":"+sigStr;
    return FALSE;
  }
  else
  {
    return TRUE;
  }
}

void Definition::_setDocumentation(const char *d,const char *docFile,int docLine,
                                   bool stripWhiteSpace,bool atTop)
{
  if (d==0) return;
  //printf("Definition::setDocumentation(%s,%s,%d,%d)\n",d,docFile,docLine,stripWhiteSpace);
  QCString doc = d;
  if (stripWhiteSpace)
  {
    doc = stripLeadingAndTrailingEmptyLines(doc);
  }
  else // don't strip whitespace
  {
    doc=d;
  }
  if (!_docsAlreadyAdded(doc))
  {
    //printf("setting docs for %s: `%s'\n",name().data(),m_doc.data());
    if (m_impl->details==0)
    {
      m_impl->details = new DocInfo;
    }
    if (m_impl->details->doc.isEmpty()) // fresh detailed description
    {
      m_impl->details->doc = doc;
    }
    else if (atTop) // another detailed description, append it to the start
    {
      m_impl->details->doc = doc+"\n\n"+m_impl->details->doc;
    }
    else // another detailed description, append it to the end
    {
      m_impl->details->doc += "\n\n"+doc;
    }
    if (docLine!=-1) // store location if valid
    {
      m_impl->details->file = docFile;
      m_impl->details->line = docLine;
    }
    else
    {
      m_impl->details->file = docFile;
      m_impl->details->line = 1;
    }
  }
}

void Definition::setDocumentation(const char *d,const char *docFile,int docLine,bool stripWhiteSpace)
{
  if (d==0) return;
  makeResident();
  _setDocumentation(d,docFile,docLine,stripWhiteSpace,FALSE);
}

#define uni_isupper(c) (QChar(c).category()==QChar::Letter_Uppercase)

// do a UTF-8 aware search for the last real character and return TRUE 
// if that is a multibyte one.
static bool lastCharIsMultibyte(const QCString &s)
{
  int l = s.length();
  int p = 0;
  int pp = -1;
  while ((p=nextUtf8CharPosition(s,l,p))<l) pp=p;
  if (pp==-1 || ((uchar)s[pp])<0x80) return FALSE;
  return TRUE;
}

void Definition::_setBriefDescription(const char *b,const char *briefFile,int briefLine)
{
  static QCString outputLanguage = Config_getEnum("OUTPUT_LANGUAGE");
  static bool needsDot = outputLanguage!="Japanese" && 
                         outputLanguage!="Chinese" &&
                         outputLanguage!="Korean";
  QCString brief = b;
  brief = brief.stripWhiteSpace();
  if (brief.isEmpty()) return;
  int bl = brief.length();
  if (bl>0 && needsDot) // add punctuation if needed
  {
    int c = brief.at(bl-1);
    switch(c)
    {
      case '.': case '!': case '?': case '>': case ':': case ')': break;
      default: 
        if (uni_isupper(brief.at(0)) && !lastCharIsMultibyte(brief)) brief+='.'; 
        break;
    }
  }

  if (m_impl->brief && !m_impl->brief->doc.isEmpty())
  {
      //printf("adding to details\n");
      _setDocumentation(brief,briefFile,briefLine,FALSE,TRUE);
  }
  else if (!_docsAlreadyAdded(brief))
  {
    //fprintf(stderr,"Definition::setBriefDescription(%s,%s,%d)\n",b,briefFile,briefLine);
    if (m_impl->brief==0)
    {
      m_impl->brief = new BriefInfo;
    }
    m_impl->brief->doc=brief;
    if (briefLine!=-1)
    {
      m_impl->brief->file = briefFile;
      m_impl->brief->line = briefLine;
    }
    else
    {
      m_impl->brief->file = briefFile;
      m_impl->brief->line = 1;
    }
  }
}

void Definition::setBriefDescription(const char *b,const char *briefFile,int briefLine) 
{ 
  if (b==0) return;
  makeResident();
  _setBriefDescription(b,briefFile,briefLine);
}

void Definition::_setInbodyDocumentation(const char *doc,const char *inbodyFile,int inbodyLine)
{
  if (m_impl->inbodyDocs==0)
  {
    m_impl->inbodyDocs = new DocInfo;
  }
  if (m_impl->inbodyDocs->doc.isEmpty()) // fresh inbody docs
  {
    m_impl->inbodyDocs->doc  = doc;
    m_impl->inbodyDocs->file = inbodyFile;
    m_impl->inbodyDocs->line = inbodyLine;
  }
  else // another inbody documentation fragment, append this to the end
  {
    m_impl->inbodyDocs->doc += QCString("\n\n")+doc;
  }
}

void Definition::setInbodyDocumentation(const char *d,const char *inbodyFile,int inbodyLine)
{
  if (d==0) return;
  makeResident();
  _setInbodyDocumentation(d,inbodyFile,inbodyLine);
}

/*! Reads a fragment of code from file \a fileName starting at 
 * line \a startLine and ending at line \a endLine (inclusive). The fragment is
 * stored in \a result. If FALSE is returned the code fragment could not be
 * found.
 *
 * The file is scanned for a opening bracket ('{') from \a startLine onward
 * The line actually containing the bracket is returned via startLine.
 * The file is scanned for a closing bracket ('}') from \a endLine backward.
 * The line actually containing the bracket is returned via endLine.
 * Note that for VHDL code the bracket search is not done.
 */
static bool readCodeFragment(const char *fileName,
                      int &startLine,int &endLine,QCString &result)
{
  static bool vhdlOpt           = Config_getBool("OPTIMIZE_OUTPUT_VHDL");
  static bool filterSourceFiles = Config_getBool("FILTER_SOURCE_FILES");
  //printf("readCodeFragment(%s,%d,%d)\n",fileName,startLine,endLine);
  if (fileName==0 || fileName[0]==0) return FALSE; // not a valid file name
  QCString filter = getFileFilter(fileName,TRUE);
  FILE *f=0;
  bool usePipe = !filter.isEmpty() && filterSourceFiles;
  if (!usePipe) // no filter given or wanted
  {
    f = portable_fopen(fileName,"r");
  }
  else // use filter
  {
    QCString cmd=filter+" \""+fileName+"\"";
    Debug::print(Debug::ExtCmd,0,"Executing popen(`%s`)\n",cmd.data());
    f = portable_popen(cmd,"r");
  }
  bool found=vhdlOpt;  // for VHDL no bracket search is possible
  if (f)
  {
    int c=0;
    int col=0;
    int lineNr=1;
    // skip until the startLine has reached
    while (lineNr<startLine && !feof(f))
    {
      while ((c=fgetc(f))!='\n' && c!=EOF) /* skip */;
      lineNr++; 
    }
    if (!feof(f))
    {
      // skip until the opening bracket or lonely : is found
      char cn=0;
      while (lineNr<=endLine && !feof(f) && !found)
      {
        int pc=0;
        while ((c=fgetc(f))!='{' && c!=':' && c!=EOF) 
        {
          //printf("parsing char `%c'\n",c);
          if (c=='\n') 
          {
            lineNr++,col=0; 
          }
          else if (c=='\t') 
          {
            col+=Config_getInt("TAB_SIZE") - (col%Config_getInt("TAB_SIZE"));
          }
          else if (pc=='/' && c=='/') // skip single line comment
          {
            while ((c=fgetc(f))!='\n' && c!=EOF) pc=c;
            if (c=='\n') lineNr++,col=0;
          }
          else if (pc=='/' && c=='*') // skip C style comment
          {
            while (((c=fgetc(f))!='/' || pc!='*') && c!=EOF) 
            {
              if (c=='\n') lineNr++,col=0;
              pc=c;
            }
          }
          else
          {
            col++;
          }
          pc = c;
        }
        if (c==':')
        {
          cn=fgetc(f);
          if (cn!=':') found=TRUE;
        }
        else if (c=='{')
        {
          found=TRUE;
        }
      }
      //printf(" -> readCodeFragment(%s,%d,%d) lineNr=%d\n",fileName,startLine,endLine,lineNr);
      if (found) 
      {
        // For code with more than one line,
        // fill the line with spaces until we are at the right column
        // so that the opening brace lines up with the closing brace
        if (endLine!=startLine)
        {
          QCString spaces;
          spaces.fill(' ',col);
          result+=spaces;
        }
        // copy until end of line
        result+=c;
        if (c==':') 
        {
          result+=cn;
          if (cn=='\n') lineNr++;
        }
        startLine=lineNr;
        const int maxLineLength=4096;
        char lineStr[maxLineLength];
        do 
        {
          //printf("reading line %d in range %d-%d\n",lineNr,startLine,endLine);
          int size_read;
          do 
          {
            // read up to maxLineLength-1 bytes, the last byte being zero
            char *p = fgets(lineStr, maxLineLength,f);
            //printf("  read %s",p);
            if (p) 
            {
              size_read=qstrlen(p); 
            }
            else  // nothing read
            {
              size_read=-1;
              lineStr[0]='\0';
            }
            result+=lineStr;
          } while (size_read == (maxLineLength-1));

          lineNr++; 
        } while (lineNr<=endLine && !feof(f));

        // strip stuff after closing bracket
        int newLineIndex = result.findRev('\n');
        int braceIndex   = result.findRev('}');
        if (braceIndex > newLineIndex) 
        {
          result.truncate(braceIndex+1);
        }
        endLine=lineNr-1;
      }
    }
    if (usePipe) 
    {
      portable_pclose(f); 
    }
    else 
    {
      fclose(f);
    }
  }
  result = transcodeCharacterStringToUTF8(result);
  return found;
}

/*! Write a reference to the source code defining this definition */
void Definition::writeSourceDef(OutputList &ol,const char *)
{
  static bool sourceBrowser = Config_getBool("SOURCE_BROWSER");
  static bool latexSourceCode = Config_getBool("LATEX_SOURCE_CODE");
  makeResident();
  ol.pushGeneratorState();
  //printf("Definition::writeSourceRef %d %p\n",bodyLine,bodyDef);
  if (sourceBrowser && 
      m_impl->body && m_impl->body->startLine!=-1 && m_impl->body->fileDef)
  {
    QCString refText = theTranslator->trDefinedAtLineInSourceFile();
    int lineMarkerPos = refText.find("@0");
    int fileMarkerPos = refText.find("@1");
    if (lineMarkerPos!=-1 && fileMarkerPos!=-1) // should always pass this.
    {
      QCString lineStr,anchorStr;
      lineStr.sprintf("%d",m_impl->body->startLine);
      anchorStr.sprintf(Htags::useHtags ? "L%d" : "l%05d",m_impl->body->startLine);
      ol.startParagraph();
      if (lineMarkerPos<fileMarkerPos) // line marker before file marker
      {
        // write text left from linePos marker
        ol.parseText(refText.left(lineMarkerPos)); 
        ol.pushGeneratorState();
        ol.disable(OutputGenerator::RTF); 
        ol.disable(OutputGenerator::Man); 
        if (!latexSourceCode)
        {
          ol.disable(OutputGenerator::Latex);
        }
        // write line link (HTML, LaTeX optionally)
        ol.writeObjectLink(0,m_impl->body->fileDef->getSourceFileBase(),
            anchorStr,lineStr);
        ol.enableAll();
        ol.disable(OutputGenerator::Html);
        if (latexSourceCode) 
        {
          ol.disable(OutputGenerator::Latex);
        }
        // write normal text (Man/RTF, Latex optionally)
        ol.docify(lineStr);
        ol.popGeneratorState();
        
        // write text between markers
        ol.parseText(refText.mid(lineMarkerPos+2,
              fileMarkerPos-lineMarkerPos-2));

        ol.pushGeneratorState();
        ol.disable(OutputGenerator::RTF); 
        ol.disable(OutputGenerator::Man); 
        if (!latexSourceCode)
        {
          ol.disable(OutputGenerator::Latex);
        }
        // write line link (HTML, LaTeX optionally)
        ol.writeObjectLink(0,m_impl->body->fileDef->getSourceFileBase(),
            0,m_impl->body->fileDef->name());
        ol.enableAll();
        ol.disable(OutputGenerator::Html);
        if (latexSourceCode) 
        {
          ol.disable(OutputGenerator::Latex);
        }
        // write normal text (Man/RTF, Latex optionally)
        ol.docify(m_impl->body->fileDef->name());
        ol.popGeneratorState();
        
        // write text right from file marker
        ol.parseText(refText.right(
              refText.length()-fileMarkerPos-2)); 
      }
      else // file marker before line marker
      {
        // write text left from file marker
        ol.parseText(refText.left(fileMarkerPos)); 
        ol.pushGeneratorState();
        ol.disable(OutputGenerator::RTF); 
        ol.disable(OutputGenerator::Man); 
        if (!latexSourceCode)
        {
          ol.disable(OutputGenerator::Latex);
        }
        // write file link (HTML only)
        ol.writeObjectLink(0,m_impl->body->fileDef->getSourceFileBase(),
            0,m_impl->body->fileDef->name());
        ol.enableAll();
        ol.disable(OutputGenerator::Html);
        if (latexSourceCode) 
        {
          ol.disable(OutputGenerator::Latex);
        }
        // write normal text (Latex/Man only)
        ol.docify(m_impl->body->fileDef->name());
        ol.popGeneratorState();
        
        // write text between markers
        ol.parseText(refText.mid(fileMarkerPos+2,
              lineMarkerPos-fileMarkerPos-2)); 

        ol.pushGeneratorState();
        ol.disable(OutputGenerator::RTF); 
        ol.disable(OutputGenerator::Man); 
        if (!latexSourceCode)
        {
          ol.disable(OutputGenerator::Latex);
        }
        ol.disableAllBut(OutputGenerator::Html); 
        // write line link (HTML only)
        ol.writeObjectLink(0,m_impl->body->fileDef->getSourceFileBase(),
            anchorStr,lineStr);
        ol.enableAll();
        ol.disable(OutputGenerator::Html);
        if (latexSourceCode) 
        {
          ol.disable(OutputGenerator::Latex);
        }
        // write normal text (Latex/Man only)
        ol.docify(lineStr);
        ol.popGeneratorState();

        // write text right from linePos marker
        ol.parseText(refText.right(
              refText.length()-lineMarkerPos-2)); 
      }
      ol.endParagraph();
    }
    else
    {
      err("error: translation error: invalid markers in trDefinedInSourceFile()\n");
    }
  }
  ol.popGeneratorState();
}

void Definition::setBodySegment(int bls,int ble) 
{
  //printf("setBodySegment(%d,%d) for %s\n",bls,ble,name().data());
  makeResident();
  if (m_impl->body==0) m_impl->body = new BodyInfo;
  m_impl->body->startLine=bls; 
  m_impl->body->endLine=ble; 
}

void Definition::setBodyDef(FileDef *fd)         
{
  makeResident();
  if (m_impl->body==0) m_impl->body = new BodyInfo;
  m_impl->body->fileDef=fd; 
}

/*! Write code of this definition into the documentation */
void Definition::writeInlineCode(OutputList &ol,const char *scopeName)
{
  makeResident();
  ol.pushGeneratorState();
  //printf("Source Fragment %s: %d-%d bodyDef=%p\n",name().data(),
  //        m_startBodyLine,m_endBodyLine,m_bodyDef);
  if (Config_getBool("INLINE_SOURCES") && 
      m_impl->body && m_impl->body->startLine!=-1 && 
      m_impl->body->endLine>=m_impl->body->startLine && m_impl->body->fileDef)
  {
    QCString codeFragment;
    int actualStart=m_impl->body->startLine,actualEnd=m_impl->body->endLine;
    if (readCodeFragment(m_impl->body->fileDef->absFilePath(),
          actualStart,actualEnd,codeFragment)
       )
    {
      //printf("Adding code fragement '%s' ext='%s'\n",
      //    codeFragment.data(),m_impl->defFileExt.data());
      ParserInterface *pIntf = Doxygen::parserManager->getParser(m_impl->defFileExt);
      pIntf->resetCodeParserState();
      //printf("Read:\n`%s'\n\n",codeFragment.data());
      MemberDef *thisMd = 0;
      if (definitionType()==TypeMember) thisMd = (MemberDef *)this;
      ol.startCodeFragment();
      pIntf->parseCode(ol,               // codeOutIntf
                       scopeName,        // scope
                       codeFragment,     // input
                       FALSE,            // isExample
                       0,                // exampleName
                       m_impl->body->fileDef,  // fileDef
                       actualStart,      // startLine
                       actualEnd,        // endLine
                       TRUE,             // inlineFragment
                       thisMd,           // memberDef
                       FALSE             // show line numbers
                      );
      ol.endCodeFragment();
    }
  }
  ol.popGeneratorState();
}

/*! Write a reference to the source code fragments in which this 
 *  definition is used.
 */
void Definition::_writeSourceRefList(OutputList &ol,const char *scopeName,
    const QCString &text,MemberSDict *members,bool /*funcOnly*/)
{
  static bool latexSourceCode = Config_getBool("LATEX_SOURCE_CODE"); 
  static bool sourceBrowser   = Config_getBool("SOURCE_BROWSER");
  static bool refLinkSource   = Config_getBool("REFERENCES_LINK_SOURCE");
  ol.pushGeneratorState();
  if (members)
  {
    ol.startParagraph();
    ol.parseText(text);
    ol.docify(" ");

    QCString ldefLine=theTranslator->trWriteList(members->count());

    QRegExp marker("@[0-9]+");
    int index=0,newIndex,matchLen;
    // now replace all markers in inheritLine with links to the classes
    while ((newIndex=marker.match(ldefLine,index,&matchLen))!=-1)
    {
      bool ok;
      ol.parseText(ldefLine.mid(index,newIndex-index));
      uint entryIndex = ldefLine.mid(newIndex+1,matchLen-1).toUInt(&ok);
      MemberDef *md=members->at(entryIndex);
      if (ok && md)
      {
        QCString scope=md->getScopeString();
        QCString name=md->name();
        //printf("class=%p scope=%s scopeName=%s\n",md->getClassDef(),scope.data(),scopeName);
        if (!scope.isEmpty() && scope!=scopeName)
        {
          if (Config_getBool("OPTIMIZE_OUTPUT_JAVA"))
          {
            name.prepend(scope+".");
          }
          else
          {
            name.prepend(scope+"::");
          }
        }
        if (!md->isObjCMethod() &&
            (md->isFunction() || md->isSlot() || 
             md->isPrototype() || md->isSignal()
            )
           ) 
        {
          name+="()";
        }
        //Definition *d = md->getOutputFileBase();
        //if (d==Doxygen::globalScope) d=md->getBodyDef();
        if (sourceBrowser &&
            !(md->isLinkable() && !refLinkSource) && 
            md->getStartBodyLine()!=-1 && 
            md->getBodyDef()
           )
        {
          //printf("md->getBodyDef()=%p global=%p\n",md->getBodyDef(),Doxygen::globalScope); 
          // for HTML write a real link
          ol.pushGeneratorState();
          //ol.disableAllBut(OutputGenerator::Html);

          ol.disable(OutputGenerator::RTF); 
          ol.disable(OutputGenerator::Man); 
          if (!latexSourceCode)
          {
            ol.disable(OutputGenerator::Latex);
          }
          QCString lineStr,anchorStr;
          anchorStr.sprintf("l%05d",md->getStartBodyLine());
          //printf("Write object link to %s\n",md->getBodyDef()->getSourceFileBase().data());
          ol.writeObjectLink(0,md->getBodyDef()->getSourceFileBase(),anchorStr,name);
          ol.popGeneratorState();

          // for the other output formats just mention the name
          ol.pushGeneratorState();
          ol.disable(OutputGenerator::Html);
          if (latexSourceCode)
          {
            ol.disable(OutputGenerator::Latex);
          }
          ol.docify(name);
          ol.popGeneratorState();
        }
        else if (md->isLinkable() /*&& d && d->isLinkable()*/)
        {
          // for HTML write a real link
          ol.pushGeneratorState();
          //ol.disableAllBut(OutputGenerator::Html); 
          ol.disable(OutputGenerator::RTF); 
          ol.disable(OutputGenerator::Man); 
          if (!latexSourceCode)
          {
            ol.disable(OutputGenerator::Latex);
          }

          ol.writeObjectLink(md->getReference(),
              md->getOutputFileBase(),
              md->anchor(),name);
          ol.popGeneratorState();

          // for the other output formats just mention the name
          ol.pushGeneratorState();
          ol.disable(OutputGenerator::Html);
          if (latexSourceCode)
          {
            ol.disable(OutputGenerator::Latex);
          }
          ol.docify(name);
          ol.popGeneratorState();
        }
        else
        {
          ol.docify(name);
        }
      }
      index=newIndex+matchLen;
    } 
    ol.parseText(ldefLine.right(ldefLine.length()-index));
    ol.writeString(".");
    ol.endParagraph();
  }
  ol.popGeneratorState();
}

void Definition::writeSourceReffedBy(OutputList &ol,const char *scopeName)
{
  makeResident();
  if (Config_getBool("REFERENCED_BY_RELATION"))
  {
    _writeSourceRefList(ol,scopeName,theTranslator->trReferencedBy(),m_impl->sourceRefByDict,FALSE);
  }
}

void Definition::writeSourceRefs(OutputList &ol,const char *scopeName)
{
  makeResident();
  if (Config_getBool("REFERENCES_RELATION"))
  {
    _writeSourceRefList(ol,scopeName,theTranslator->trReferences(),m_impl->sourceRefsDict,TRUE);
  }
}

bool Definition::hasDocumentation() const
{ 
  static bool extractAll    = Config_getBool("EXTRACT_ALL"); 
  //static bool sourceBrowser = Config_getBool("SOURCE_BROWSER");
  makeResident();
  bool hasDocs = 
         (m_impl->details    && !m_impl->details->doc.isEmpty())    || // has detailed docs
         (m_impl->brief      && !m_impl->brief->doc.isEmpty())      || // has brief description
         (m_impl->inbodyDocs && !m_impl->inbodyDocs->doc.isEmpty()) || // has inbody docs
         extractAll //||                   // extract everything
  //       (sourceBrowser && m_impl->body && 
  //        m_impl->body->startLine!=-1 && m_impl->body->fileDef)
         ; // link to definition
  return hasDocs;
}

bool Definition::hasUserDocumentation() const
{
  makeResident();
  bool hasDocs = 
         (m_impl->details    && !m_impl->details->doc.isEmpty()) ||
         (m_impl->brief      && !m_impl->brief->doc.isEmpty())   ||
         (m_impl->inbodyDocs && !m_impl->inbodyDocs->doc.isEmpty());
  return hasDocs;
}

void Definition::addSourceReferencedBy(MemberDef *md)
{
  if (md)
  {
    makeResident();
    QCString name  = md->name();
    QCString scope = md->getScopeString();

    if (!scope.isEmpty())
    {
      name.prepend(scope+"::");
    }

    if (m_impl->sourceRefByDict==0)
    {
      m_impl->sourceRefByDict = new MemberSDict;
    }
    if (m_impl->sourceRefByDict->find(name)==0)
    {
      m_impl->sourceRefByDict->inSort(name,md);
    }
  }
}

void Definition::addSourceReferences(MemberDef *md)
{
  if (md)
  {
    QCString name  = md->name();
    QCString scope = md->getScopeString();
    makeResident();

    if (!scope.isEmpty())
    {
      name.prepend(scope+"::");
    }

    if (m_impl->sourceRefsDict==0)
    {
      m_impl->sourceRefsDict = new MemberSDict;
    }
    if (m_impl->sourceRefsDict->find(name)==0)
    {
      m_impl->sourceRefsDict->inSort(name,md);
    }
  }
}

Definition *Definition::findInnerCompound(const char *)
{
  return 0;
}

void Definition::addInnerCompound(Definition *)
{
  err("error: Definition::addInnerCompound() called\n");
}

QCString Definition::qualifiedName() const
{
  static int count=0;
  count++;
  makeResident();
  if (!m_impl->qualifiedName.isEmpty()) 
  {
    count--;
    return m_impl->qualifiedName;
  }
#if 0
  if (count>20)
  {
    printf("Definition::qualifiedName() Infinite recursion detected! Type=%d\n",definitionType());
    printf("Trace:\n");
    Definition *d = (Definition *)this;
    for (int i=0;d && i<20;i++)
    {
      printf("  %s\n",d->name().data());
      d = d->getOuterScope();
    }
  }
#endif
  
  //printf("start %s::qualifiedName() localName=%s\n",name().data(),m_impl->localName.data());
  if (m_impl->outerScope==0) 
  {
    if (m_impl->localName=="<globalScope>") 
    {
      count--;
      return "";
    }
    else 
    {
      count--;
      return m_impl->localName; 
    }
  }

  if (m_impl->outerScope->name()=="<globalScope>")
  {
    m_impl->qualifiedName = m_impl->localName;
  }
  else
  {
    m_impl->qualifiedName = m_impl->outerScope->qualifiedName()+"::"+m_impl->localName;
  }
  //printf("end %s::qualifiedName()=%s\n",name().data(),m_impl->qualifiedName.data());
  count--;
  return m_impl->qualifiedName;
};

void Definition::setOuterScope(Definition *d) 
{
  makeResident();
  if (m_impl->outerScope!=d)
  { 
    m_impl->qualifiedName.resize(0); // flush cached scope name
    m_impl->outerScope = d; 
  }
  m_impl->hidden = m_impl->hidden || d->isHidden();
}

QCString Definition::localName() const
{
  makeResident();
  return m_impl->localName;
}

void Definition::makePartOfGroup(GroupDef *gd)
{
  makeResident();
  if (m_impl->partOfGroups==0) m_impl->partOfGroups = new GroupList;
  m_impl->partOfGroups->append(gd);
}

void Definition::setRefItems(const QList<ListItemInfo> *sli)
{
  //printf("%s::setRefItems()\n",name().data());
  if (sli)
  {
    makeResident();
    // deep copy the list
    if (m_impl->xrefListItems==0) 
    {
      m_impl->xrefListItems=new QList<ListItemInfo>;
      m_impl->xrefListItems->setAutoDelete(TRUE);
    }
    QListIterator<ListItemInfo> slii(*sli);
    ListItemInfo *lii;
    for (slii.toFirst();(lii=slii.current());++slii)
    {
      m_impl->xrefListItems->append(new ListItemInfo(*lii));
    } 
  }
}

void Definition::mergeRefItems(Definition *d)
{
  //printf("%s::mergeRefItems()\n",name().data());
  LockingPtr< QList<ListItemInfo> > xrefList = d->xrefListItems();
  if (xrefList!=0)
  {
    makeResident();
    // deep copy the list
    if (m_impl->xrefListItems==0) 
    {
      m_impl->xrefListItems=new QList<ListItemInfo>;
      m_impl->xrefListItems->setAutoDelete(TRUE);
    }
    QListIterator<ListItemInfo> slii(*xrefList);
    ListItemInfo *lii;
    for (slii.toFirst();(lii=slii.current());++slii)
    {
      if (_getXRefListId(lii->type)==-1)
      {
        m_impl->xrefListItems->append(new ListItemInfo(*lii));
      }
    } 
  }
}

int Definition::_getXRefListId(const char *listName) const
{
  makeResident();
  if (m_impl->xrefListItems)
  {
    QListIterator<ListItemInfo> slii(*m_impl->xrefListItems);
    ListItemInfo *lii;
    for (slii.toFirst();(lii=slii.current());++slii)
    {
      if (strcmp(lii->type,listName)==0)
      {
        return lii->itemId;
      }
    }
  }
  return -1;
}

LockingPtr< QList<ListItemInfo> > Definition::xrefListItems() const
{
  makeResident();
  return LockingPtr< QList<ListItemInfo> >(this,m_impl->xrefListItems);
}


QCString Definition::convertNameToFile(const char *name,bool allowDots) const
{
  makeResident();
  if (!m_impl->ref.isEmpty())
  {
    return name;
  }
  else
  {
    return ::convertNameToFile(name,allowDots);
  }
}

QCString Definition::pathFragment() const
{
  makeResident();
  QCString result;
  if (m_impl->outerScope && m_impl->outerScope!=Doxygen::globalScope)
  {
    result = m_impl->outerScope->pathFragment();
  }
  if (isLinkable())
  {
    if (!result.isEmpty()) result+="/";
    if (definitionType()==Definition::TypeGroup && ((const GroupDef*)this)->groupTitle())
    {
      result+=((const GroupDef*)this)->groupTitle();
    }
    else if (definitionType()==Definition::TypePage && !((const PageDef*)this)->title().isEmpty())
    {
      result+=((const PageDef*)this)->title();
    }
    else
    {
      result+=m_impl->localName;
    }
  }
  else
  {
    result+=m_impl->localName;
  }
  return result;
}

void Definition::writePathFragment(OutputList &ol) const
{
  makeResident();
  if (m_impl->outerScope && m_impl->outerScope!=Doxygen::globalScope)
  {
    m_impl->outerScope->writePathFragment(ol);
  }
  ol.writeString("      <li class=\"navelem\">");
  if (isLinkable())
  {
    if (definitionType()==Definition::TypeGroup && ((const GroupDef*)this)->groupTitle())
    {
      ol.writeObjectLink(getReference(),getOutputFileBase(),0,((const GroupDef*)this)->groupTitle());
    }
    else if (definitionType()==Definition::TypePage && !((const PageDef*)this)->title().isEmpty())
    {
      ol.writeObjectLink(getReference(),getOutputFileBase(),0,((const PageDef*)this)->title());
    }
    else if (definitionType()==Definition::TypeClass)
    {
      QCString name = m_impl->localName;
      if (name.right(2)=="-p" || name.right(2)=="-g")
      {
        name = name.left(name.length()-2);
      }
      ol.writeObjectLink(getReference(),getOutputFileBase(),0,name);
    }
    else
    {
      ol.writeObjectLink(getReference(),getOutputFileBase(),0,m_impl->localName);
    }
  }
  else
  {
    ol.startBold();
    ol.docify(m_impl->localName);
    ol.endBold();
  }
  ol.writeString("      </li>\n");
}

void Definition::writeNavigationPath(OutputList &ol) const
{
  static bool generateTreeView = Config_getBool("GENERATE_TREEVIEW");
  static bool hasCustomFooter = !Config_getString("HTML_FOOTER").isEmpty();

  ol.pushGeneratorState();
  ol.disableAllBut(OutputGenerator::Html);

  if (generateTreeView)
  {
    ol.writeString("</div>\n");
  }

  ol.writeString("  <div id=\"nav-path\" class=\"navpath\">\n");
  ol.writeString("    <ul>\n");
  writePathFragment(ol);
  if (!hasCustomFooter)
  {
    if (generateTreeView) // write the doxygen logo as part of the navigation bar
    {
      ol.writeString("      <li class=\"footer\">");
      ol.writeLogo();
      ol.writeString("</li>\n");
    }
    ol.writeString("    </ul>\n");
    ol.writeString("  </div>\n");
  }

  ol.popGeneratorState();
}

QCString Definition::symbolName() const 
{ 
  return m_symbolName; 
}

//----------------------

QCString Definition::documentation() const 
{ 
  makeResident();
  return m_impl->details ? m_impl->details->doc : QCString(""); 
}

int Definition::docLine() const 
{ 
  makeResident();
  return m_impl->details ? m_impl->details->line : 1; 
}

QCString Definition::docFile() const 
{ 
  makeResident();
  return m_impl->details ? m_impl->details->file : QCString("<"+m_name+">"); 
}

//----------------------

QCString Definition::briefDescription() const 
{ 
  makeResident();
  return m_impl->brief ? m_impl->brief->doc : QCString(""); 
}

QCString Definition::briefDescriptionAsTooltip() const
{
  makeResident();
  if (m_impl->brief)
  {
    if (m_impl->brief->tooltip.isEmpty() && !m_impl->brief->doc.isEmpty())
    {
      static bool reentering=FALSE; 
      if (!reentering)
      {
        MemberDef *md = definitionType()==TypeMember ? (MemberDef*)this : 0;
        const Definition *scope = definitionType()==TypeMember ? getOuterScope() : this;
        reentering=TRUE; // prevent requests for tooltips while parsing a tooltip
        m_impl->brief->tooltip = parseCommentAsText(
            scope,md,
            m_impl->brief->doc,
            m_impl->brief->file,
            m_impl->brief->line);
        reentering=FALSE;
      }
    }
    return m_impl->brief->tooltip;
  }
  return QCString("");
}

int Definition::briefLine() const 
{ 
  makeResident();
  return m_impl->brief ? m_impl->brief->line : 1; 
}

QCString Definition::briefFile() const 
{ 
  makeResident();
  return m_impl->brief ? m_impl->brief->file : QCString("<"+m_name+">"); 
}

//----------------------

QCString Definition::inbodyDocumentation() const
{
  makeResident();
  return m_impl->inbodyDocs ? m_impl->inbodyDocs->doc : QCString(""); 
}

int Definition::inbodyLine() const 
{ 
  makeResident();
  return m_impl->inbodyDocs ? m_impl->inbodyDocs->line : 1; 
}

QCString Definition::inbodyFile() const 
{ 
  makeResident();
  return m_impl->inbodyDocs ? m_impl->inbodyDocs->file : QCString("<"+m_name+">"); 
}


//----------------------

QCString Definition::getDefFileName() const 
{ 
  makeResident();
  return m_impl->defFileName; 
}

QCString Definition::getDefFileExtension() const 
{ 
  makeResident();
  return m_impl->defFileExt; 
}

int Definition::getDefLine() const 
{ 
  makeResident();
  return m_impl->defLine; 
}

bool Definition::isHidden() const
{
  makeResident();
  return m_impl->hidden;
}

bool Definition::isVisibleInProject() const 
{ 
  return isLinkableInProject() && !m_impl->hidden; 
}

bool Definition::isVisible() const
{ 
  return isLinkable() && !m_impl->hidden; 
}

bool Definition::isArtificial() const
{
  return m_impl->isArtificial;
}

QCString Definition::getReference() const 
{ 
  makeResident();
  return m_impl->ref; 
}

bool Definition::isReference() const 
{ 
  makeResident();
  return !m_impl->ref.isEmpty(); 
}

int Definition::getStartBodyLine() const         
{ 
  makeResident();
  return m_impl->body ? m_impl->body->startLine : -1; 
}

int Definition::getEndBodyLine() const           
{ 
  makeResident();
  return m_impl->body ? m_impl->body->endLine : -1; 
}

FileDef *Definition::getBodyDef()                
{ 
  makeResident();
  return m_impl->body ? m_impl->body->fileDef : 0; 
}

LockingPtr<GroupList> Definition::partOfGroups() const 
{ 
  makeResident();
  return LockingPtr<GroupList>(this,m_impl->partOfGroups); 
}

Definition *Definition::getOuterScope() const 
{ 
  makeResident();
  return m_impl->outerScope; 
}

LockingPtr<MemberSDict> Definition::getReferencesMembers() const 
{ 
  makeResident();
  return LockingPtr<MemberSDict>(this,m_impl->sourceRefsDict); 
}

LockingPtr<MemberSDict> Definition::getReferencedByMembers() const 
{ 
  makeResident();
  return LockingPtr<MemberSDict>(this,m_impl->sourceRefByDict); 
}

void Definition::setReference(const char *r) 
{ 
  makeResident();
  m_impl->ref=r; 
}

void Definition::_setSymbolName(const QCString &name) 
{ 
  m_symbolName=name; 
}

void Definition::setHidden(bool b) 
{ 
  makeResident();
  m_impl->hidden = m_impl->hidden || b; 
}

void Definition::setArtificial(bool b)
{
  makeResident();
  m_impl->isArtificial = b;
}

void Definition::setLocalName(const QCString name) 
{ 
  makeResident();
  m_impl->localName=name; 
}

void Definition::makeResident() const
{
}


void Definition::flushToDisk() const
{
  //printf("%p: Definition::flushToDisk()\n",this);
  Definition *that = (Definition *)this;
  //printf("Definition::flushToDisk(): pos=%d\n",(int)m_storagePos); 
  marshalUInt(Doxygen::symbolStorage,START_MARKER);
  marshalSectionDict  (Doxygen::symbolStorage,m_impl->sectionDict);
  marshalMemberSDict  (Doxygen::symbolStorage,m_impl->sourceRefByDict);
  marshalMemberSDict  (Doxygen::symbolStorage,m_impl->sourceRefsDict);
  marshalItemInfoList (Doxygen::symbolStorage,m_impl->xrefListItems);
  marshalGroupList    (Doxygen::symbolStorage,m_impl->partOfGroups);
  marshalDocInfo      (Doxygen::symbolStorage,m_impl->details);
  marshalDocInfo      (Doxygen::symbolStorage,m_impl->inbodyDocs);
  marshalBriefInfo    (Doxygen::symbolStorage,m_impl->brief);
  marshalBodyInfo     (Doxygen::symbolStorage,m_impl->body);
  marshalQCString     (Doxygen::symbolStorage,m_impl->docSignatures);
  marshalQCString     (Doxygen::symbolStorage,m_impl->localName);
  marshalQCString     (Doxygen::symbolStorage,m_impl->qualifiedName);
  marshalQCString     (Doxygen::symbolStorage,m_impl->ref);
  marshalBool         (Doxygen::symbolStorage,m_impl->hidden);
  marshalBool         (Doxygen::symbolStorage,m_impl->isArtificial);
  marshalObjPointer   (Doxygen::symbolStorage,m_impl->outerScope);
  marshalQCString     (Doxygen::symbolStorage,m_impl->defFileName);
  marshalInt          (Doxygen::symbolStorage,m_impl->defLine);
  marshalQCString     (Doxygen::symbolStorage,m_impl->defFileExt);
  marshalUInt(Doxygen::symbolStorage,END_MARKER);
  delete that->m_impl;
  that->m_impl = 0;
}

void Definition::loadFromDisk() const
{
  //printf("%p: Definition::loadFromDisk()\n",this);
  Definition *that = (Definition *)this;
  assert(m_impl==0);
  that->m_impl = new DefinitionImpl;
  uint marker = unmarshalUInt(Doxygen::symbolStorage);
  assert(marker==START_MARKER);
  m_impl->sectionDict     = unmarshalSectionDict  (Doxygen::symbolStorage);
  m_impl->sourceRefByDict = unmarshalMemberSDict  (Doxygen::symbolStorage);
  m_impl->sourceRefsDict  = unmarshalMemberSDict  (Doxygen::symbolStorage);
  m_impl->xrefListItems   = unmarshalItemInfoList (Doxygen::symbolStorage);
  m_impl->partOfGroups    = unmarshalGroupList    (Doxygen::symbolStorage);
  m_impl->details         = unmarshalDocInfo      (Doxygen::symbolStorage);
  m_impl->inbodyDocs      = unmarshalDocInfo      (Doxygen::symbolStorage);
  m_impl->brief           = unmarshalBriefInfo    (Doxygen::symbolStorage);
  m_impl->body            = unmarshalBodyInfo     (Doxygen::symbolStorage);
  m_impl->docSignatures   = unmarshalQCString     (Doxygen::symbolStorage);
  m_impl->localName       = unmarshalQCString     (Doxygen::symbolStorage);
  m_impl->qualifiedName   = unmarshalQCString     (Doxygen::symbolStorage);
  m_impl->ref             = unmarshalQCString     (Doxygen::symbolStorage);
  m_impl->hidden          = unmarshalBool         (Doxygen::symbolStorage);
  m_impl->isArtificial    = unmarshalBool         (Doxygen::symbolStorage);
  m_impl->outerScope      = (Definition *)unmarshalObjPointer   (Doxygen::symbolStorage);
  m_impl->defFileName     = unmarshalQCString     (Doxygen::symbolStorage);
  m_impl->defLine         = unmarshalInt          (Doxygen::symbolStorage);
  m_impl->defFileExt      = unmarshalQCString     (Doxygen::symbolStorage);
  marker = unmarshalUInt(Doxygen::symbolStorage);
  assert(marker==END_MARKER);
}

