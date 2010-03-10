/******************************************************************************
 *
 * 
 *
 *
 * Copyright (C) 1997-2010 by Dimitri van Heesch.
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

#include "tagreader.h"

#include <stdio.h>
#include <stdarg.h>

#include <qxml.h>
#include <qstack.h>
#include <qdict.h>
#include <qfileinfo.h>
#include <qlist.h>
#include <qstring.h>
#include <qstringlist.h>

#include "entry.h"
#include "classdef.h"
#include "doxygen.h"
#include "util.h"
#include "message.h"
#include "defargs.h"
//#include "reflist.h"

/*! Information about an linkable anchor */
class TagAnchorInfo
{
  public:
    TagAnchorInfo(const QString &f,const QString &l) : label(l), fileName(f) {}
    QString label;
    QString fileName;
};

class TagAnchorInfoList : public QList<TagAnchorInfo>
{
  public: 
    TagAnchorInfoList() : QList<TagAnchorInfo>() { setAutoDelete(TRUE); }
    virtual ~TagAnchorInfoList() {}
};

/*! Container for member specific info that can be read from a tagfile */
class TagMemberInfo
{
  public:
    TagMemberInfo() : prot(Public), virt(Normal), isStatic(FALSE) {}
    QString type;
    QString name;
    QString anchorFile;
    QString anchor;
    QString arglist;
    QString kind;
    TagAnchorInfoList docAnchors;
    Protection prot;
    Specifier virt;
    bool isStatic; 
};

/*! Container for class specific info that can be read from a tagfile */
class TagClassInfo
{
  public:
    enum Kind { Class, Struct, Union, Interface, Exception, Protocol, Category };
    TagClassInfo() { bases=0, templateArguments=0; members.setAutoDelete(TRUE); isObjC=FALSE; }
   ~TagClassInfo() { delete bases; delete templateArguments; }
    QString name;
    QString filename;
    TagAnchorInfoList docAnchors;
    QList<BaseInfo> *bases;
    QList<TagMemberInfo> members;
    QList<QString> *templateArguments;
    QStringList classList;
    Kind kind;
    bool isObjC;
};

/*! Container for namespace specific info that can be read from a tagfile */
class TagNamespaceInfo
{
  public:
    TagNamespaceInfo() { members.setAutoDelete(TRUE); }
    QString name;
    QString filename;
    QStringList classList;
    QStringList namespaceList;
    TagAnchorInfoList docAnchors;
    QList<TagMemberInfo> members;
};

/*! Container for package specific info that can be read from a tagfile */
class TagPackageInfo
{
  public:
    TagPackageInfo() { members.setAutoDelete(TRUE); }
    QString name;
    QString filename;
    TagAnchorInfoList docAnchors;
    QList<TagMemberInfo> members;
    QStringList classList;
};

class TagIncludeInfo
{
  public:
    QString id;
    QString name;
    QString text;
    bool isLocal;
    bool isImported;
};

/*! Container for file specific info that can be read from a tagfile */
class TagFileInfo
{
  public:
    TagFileInfo() { members.setAutoDelete(TRUE); includes.setAutoDelete(TRUE); }
    QString name;
    QString path;
    QString filename;
    TagAnchorInfoList docAnchors;
    QList<TagMemberInfo> members;
    QStringList classList;
    QStringList namespaceList;
    QList<TagIncludeInfo> includes;
};

/*! Container for group specific info that can be read from a tagfile */
class TagGroupInfo
{
  public:
    TagGroupInfo() { members.setAutoDelete(TRUE); }
    QString name;
    QString title;
    QString filename;
    TagAnchorInfoList docAnchors;
    QList<TagMemberInfo> members;
    QStringList subgroupList;
    QStringList classList;
    QStringList namespaceList;
    QStringList fileList;
    QStringList pageList;
    QStringList dirList;
};

/*! Container for page specific info that can be read from a tagfile */
class TagPageInfo
{
  public:
    QString name;
    QString title;
    QString filename;
    TagAnchorInfoList docAnchors;
};

/*! Container for directory specific info that can be read from a tagfile */
class TagDirInfo
{
  public:
    QString name;
    QString filename;
    QString path;
    QStringList subdirList;
    QStringList fileList;
    TagAnchorInfoList docAnchors;
};

/*! Tag file parser. 
 *  Reads an XML-structured tagfile and builds up the structure in
 *  memory. The method buildLists() is used to transfer/translate 
 *  the structures to the doxygen engine.
 */
class TagFileParser : public QXmlDefaultHandler
{
    enum State { Invalid,
                 InClass,
                 InFile,
                 InNamespace,
                 InGroup,
                 InPage,
                 InMember,
                 InPackage,
                 InDir,
                 InTempArgList
               };
    class StartElementHandler
    {
        typedef void (TagFileParser::*Handler)(const QXmlAttributes &attrib); 
      public:
        StartElementHandler(TagFileParser *parent, Handler h) : m_parent(parent), m_handler(h) {}
        void operator()(const QXmlAttributes &attrib) { (m_parent->*m_handler)(attrib); }
      private:
        TagFileParser *m_parent;
        Handler m_handler;
    };

    class EndElementHandler
    {
        typedef void (TagFileParser::*Handler)(); 
      public:
        EndElementHandler(TagFileParser *parent, Handler h) : m_parent(parent), m_handler(h) {}
        void operator()() { (m_parent->*m_handler)(); }
      private:
        TagFileParser *m_parent;
        Handler m_handler;
    };

  public:
    TagFileParser(const char *tagName) : m_startElementHandlers(17),
                                         m_endElementHandlers(17),
                                         m_tagName(tagName)
    {
      m_startElementHandlers.setAutoDelete(TRUE);
      m_endElementHandlers.setAutoDelete(TRUE);
    }
    
    void setDocumentLocator ( QXmlLocator * locator )
    {
      m_locator = locator;
    }

    void setFileName( const QString &fileName )
    {
      m_inputFileName = fileName;
    }

    void warn(const char *fmt)
    {
      ::warn(m_inputFileName,m_locator->lineNumber(),fmt);
    }
    void warn(const char *fmt,const char *s)
    {
      ::warn(m_inputFileName,m_locator->lineNumber(),fmt,s);
    }

    void startCompound( const QXmlAttributes& attrib )
    {
      m_curString = "";
      QString kind = attrib.value("kind");
      QString isObjC = attrib.value("objc");
      if (kind=="class")
      {
        m_curClass = new TagClassInfo;
        m_curClass->kind = TagClassInfo::Class;
        m_state = InClass;
      }
      else if (kind=="struct")
      {
        m_curClass = new TagClassInfo;
        m_curClass->kind = TagClassInfo::Struct;
        m_state = InClass;
      }
      else if (kind=="union")
      {
        m_curClass = new TagClassInfo;
        m_curClass->kind = TagClassInfo::Union;
        m_state = InClass;
      }
      else if (kind=="interface")
      {
        m_curClass = new TagClassInfo;
        m_curClass->kind = TagClassInfo::Interface;
        m_state = InClass;
      }
      else if (kind=="exception")
      {
        m_curClass = new TagClassInfo;
        m_curClass->kind = TagClassInfo::Exception;
        m_state = InClass;
      }
      else if (kind=="protocol")
      {
        m_curClass = new TagClassInfo;
        m_curClass->kind = TagClassInfo::Protocol;
        m_state = InClass;
      }
      else if (kind=="category")
      {
        m_curClass = new TagClassInfo;
        m_curClass->kind = TagClassInfo::Category;
        m_state = InClass;
      }
      else if (kind=="file")
      {
        m_curFile = new TagFileInfo;
        m_state = InFile;
      }
      else if (kind=="namespace")
      {
        m_curNamespace = new TagNamespaceInfo;
        m_state = InNamespace;
      }
      else if (kind=="group")
      {
        m_curGroup = new TagGroupInfo;
        m_state = InGroup;
      }
      else if (kind=="page")
      {
        m_curPage = new TagPageInfo;
        m_state = InPage;
      }
      else if (kind=="package")
      {
        m_curPackage = new TagPackageInfo;
        m_state = InPackage;
      }
      else if (kind=="dir")
      {
        m_curDir = new TagDirInfo;
        m_state = InDir;
      }
      else
      {
        warn("Warning: Unknown compound attribute `%s' found!\n",kind.data());
      }
      if (isObjC=="yes" && m_curClass)
      {
        m_curClass->isObjC = TRUE; 
      }
    }

    void endCompound()
    {
      switch (m_state)
      {
        case InClass:     m_tagFileClasses.append(m_curClass); 
                          m_curClass=0; break; 
        case InFile:      m_tagFileFiles.append(m_curFile); 
                          m_curFile=0; break; 
        case InNamespace: m_tagFileNamespaces.append(m_curNamespace); 
                          m_curNamespace=0; break; 
        case InGroup:     m_tagFileGroups.append(m_curGroup); 
                          m_curGroup=0; break; 
        case InPage:      m_tagFilePages.append(m_curPage); 
                          m_curPage=0; break; 
        case InDir:       m_tagFileDirs.append(m_curDir);
                          m_curDir=0; break;
        case InPackage:   m_tagFilePackages.append(m_curPackage); 
                          m_curPackage=0; break; 
        default:
                          warn("Warning: tag `compound' was not expected!\n");
      }
    }

    void startMember( const QXmlAttributes& attrib)
    {
      m_curMember = new TagMemberInfo;
      m_curMember->kind = attrib.value("kind");
      QString protStr   = attrib.value("protection");
      QString virtStr   = attrib.value("virtualness");
      QString staticStr = attrib.value("static");
      if (protStr=="protected")
      {
        m_curMember->prot = Protected;
      }
      else if (protStr=="private")
      {
        m_curMember->prot = Private;
      }
      if (virtStr=="virtual")
      {
        m_curMember->virt = Virtual;
      }
      else if (virtStr=="pure")
      {
        m_curMember->virt = Pure;
      }
      if (staticStr=="yes")
      {
        m_curMember->isStatic = TRUE;
      }
      m_stateStack.push(new State(m_state));
      m_state = InMember;
    }

    void endMember()
    {
      m_state = *m_stateStack.top();
      m_stateStack.remove();
      switch(m_state)
      {
        case InClass:     m_curClass->members.append(m_curMember); break;
        case InFile:      m_curFile->members.append(m_curMember); break;
        case InNamespace: m_curNamespace->members.append(m_curMember); break;
        case InGroup:     m_curGroup->members.append(m_curMember); break;
        case InPackage:   m_curPackage->members.append(m_curMember); break;
        default:   warn("Warning: Unexpected tag `member' found\n"); break; 
      }
    }

    void endDocAnchor()
    {
      switch(m_state)
      {
        case InClass:     m_curClass->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        case InFile:      m_curFile->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        case InNamespace: m_curNamespace->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        case InGroup:     m_curGroup->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        case InPage:      m_curPage->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        case InMember:    m_curMember->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        case InPackage:   m_curPackage->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        case InDir:       m_curDir->docAnchors.append(new TagAnchorInfo(m_fileName,m_curString)); break;
        default:   warn("Warning: Unexpected tag `member' found\n"); break; 
      }
    }

    void endClass()
    {
      switch(m_state)
      {
        case InClass:     m_curClass->classList.append(m_curString); break;
        case InFile:      m_curFile->classList.append(m_curString); break;
        case InNamespace: m_curNamespace->classList.append(m_curString); break;
        case InGroup:     m_curGroup->classList.append(m_curString); break;
        case InPackage:   m_curPackage->classList.append(m_curString); break;
        default:   warn("Warning: Unexpected tag `class' found\n"); break; 
      }
    }

    void endNamespace()
    {
      switch(m_state)
      {
        case InNamespace: m_curNamespace->classList.append(m_curString); break;
        case InFile:      m_curFile->namespaceList.append(m_curString); break;
        case InGroup:     m_curGroup->namespaceList.append(m_curString); break;
        default:   warn("Warning: Unexpected tag `namespace' found\n"); break; 
      }
    }

    void endFile()
    {
      switch(m_state)
      {
        case InGroup:      m_curGroup->fileList.append(m_curString); break;
        case InDir:        m_curDir->fileList.append(m_curString); break;
        default:   warn("Warning: Unexpected tag `file' found\n"); break; 
      }
    }

    void endPage()
    {
      switch(m_state)
      {
        case InGroup:      m_curGroup->fileList.append(m_curString); break;
        default:   warn("Warning: Unexpected tag `page' found\n"); break; 
      }
    }

    void endDir()
    {
      switch(m_state)
      {
        case InDir:      m_curDir->subdirList.append(m_curString); break;
        default:   warn("Warning: Unexpected tag `page' found\n"); break; 
      }
    }

    void startStringValue(const QXmlAttributes& )
    {
      m_curString = "";
    }

    void startDocAnchor(const QXmlAttributes& attrib )
    {
      m_fileName = attrib.value("file");
      m_curString = "";
    }

    void endType()
    {
      if (m_state==InMember)
      {
        m_curMember->type = m_curString; 
      }
      else
      {
        warn("Warning: Unexpected tag `type' found\n");
      }
    }

    void endName()
    {
      switch (m_state)
      {
        case InClass:     m_curClass->name     = m_curString; break;
        case InFile:      m_curFile->name      = m_curString; break;
        case InNamespace: m_curNamespace->name = m_curString; break;
        case InGroup:     m_curGroup->name     = m_curString; break;
        case InPage:      m_curPage->name      = m_curString; break;
        case InDir:       m_curDir->name       = m_curString; break;
        case InMember:    m_curMember->name    = m_curString; break;
        case InPackage:   m_curPackage->name   = m_curString; break;
        default: warn("Warning: Unexpected tag `name' found\n"); break; 
      }
    }

    void startBase(const QXmlAttributes& attrib )
    {
      m_curString="";
      if (m_state==InClass && m_curClass)
      {
        QString protStr = attrib.value("protection");
        QString virtStr = attrib.value("virtualness");
        Protection prot = Public;
        Specifier  virt = Normal;
        if (protStr=="protected")
        {
          prot = Protected;
        }
        else if (protStr=="private")
        {
          prot = Private;
        }
        if (virtStr=="virtual")
        {
          virt = Virtual;
        }
        if (m_curClass->bases==0) 
        {
          m_curClass->bases = new QList<BaseInfo>;
          m_curClass->bases->setAutoDelete(TRUE);
        }
        m_curClass->bases->append(new BaseInfo(m_curString,prot,virt));
      }
      else
      {
        warn("Warning: Unexpected tag `base' found\n");
      }
    }

    void endBase()
    {
      if (m_state==InClass && m_curClass)
      {
        m_curClass->bases->getLast()->name = m_curString;
      }
      else
      {
        warn("Warning: Unexpected tag `base' found\n");
      }
    }

    void startIncludes(const QXmlAttributes& attrib )
    {
      if (m_state==InFile && m_curFile)
      {
        m_curIncludes = new TagIncludeInfo;
        m_curIncludes->id = attrib.value("id");
        m_curIncludes->name = attrib.value("name");
        m_curIncludes->isLocal = attrib.value("local")=="yes" ? TRUE : FALSE;
        m_curIncludes->isImported = attrib.value("imported")=="yes" ? TRUE : FALSE;
        m_curFile->includes.append(m_curIncludes);
      }
      else
      {
        warn("Warning: Unexpected tag `includes' found\n");
      }
      m_curString="";
    }

    void endIncludes()
    {
      m_curIncludes->text = m_curString;
    }

    void endTemplateArg()
    {
      if (m_state==InClass && m_curClass)
      {
        if (m_curClass->templateArguments==0) 
        {
          m_curClass->templateArguments = new QList<QString>;
          m_curClass->templateArguments->setAutoDelete(TRUE);
        }
        m_curClass->templateArguments->append(new QString(m_curString));
      }
      else
      {
        warn("Warning: Unexpected tag `templarg' found\n");
      }
    }

    void endFilename()
    {
      switch (m_state)
      {
        case InClass:     m_curClass->filename     = m_curString;    break;
        case InNamespace: m_curNamespace->filename = m_curString;    break;
        case InFile:      m_curFile->filename      = m_curString;    break;
        case InGroup:     m_curGroup->filename     = m_curString;    break;
        case InPage:      m_curPage->filename      = m_curString;    break;
        case InPackage:   m_curPackage->filename   = m_curString;    break;
        case InDir:       m_curDir->filename       = m_curString;    break;
        default: warn("Warning: Unexpected tag `filename' found\n"); break; 
      }
    }

    void endPath()
    {
      switch (m_state)
      {
        case InFile:      m_curFile->path          = m_curString;    break;
        case InDir:       m_curDir->path           = m_curString;    break;
        default: warn("Warning: Unexpected tag `path' found\n");     break; 
      }
    }
    
    void endAnchor()
    {
      if (m_state==InMember)
      {
        m_curMember->anchor = m_curString; 
      }
      else
      {
        warn("Warning: Unexpected tag `anchor' found\n");
      }
    }
    
    void endAnchorFile()
    {
      if (m_state==InMember)
      {
        m_curMember->anchorFile = m_curString; 
      }
      else
      {
        warn("Warning: Unexpected tag `anchorfile' found\n");
      }
    }
    
    void endArglist()
    {
      if (m_state==InMember)
      {
        m_curMember->arglist = m_curString; 
      }
      else
      {
        warn("Warning: Unexpected tag `arglist' found\n");
      }
    }
    void endTitle()
    {
      switch (m_state)
      {
        case InGroup:     m_curGroup->title     = m_curString;    break;
        case InPage:      m_curPage->title      = m_curString;    break;
        default: warn("Warning: Unexpected tag `title' found\n"); break; 
      }
    }

    void endSubgroup()
    {
      if (m_state==InGroup)
      {
        m_curGroup->subgroupList.append(m_curString);
      }
      else
      {
        warn("Warning: Unexpected tag `subgroup' found\n");
      }
    }

    void startIgnoreElement(const QXmlAttributes& )
    {
    }

    void endIgnoreElement()
    {
    }

    bool startDocument()
    {
      m_state = Invalid;

      m_curClass=0;
      m_curNamespace=0;
      m_curFile=0;
      m_curGroup=0;
      m_curPage=0;
      m_curPackage=0;
      m_curDir=0;

      m_stateStack.setAutoDelete(TRUE);
      m_tagFileClasses.setAutoDelete(TRUE);
      m_tagFileFiles.setAutoDelete(TRUE);
      m_tagFileNamespaces.setAutoDelete(TRUE);
      m_tagFileGroups.setAutoDelete(TRUE);
      m_tagFilePages.setAutoDelete(TRUE);
      m_tagFilePackages.setAutoDelete(TRUE);
      m_tagFileDirs.setAutoDelete(TRUE);

      m_startElementHandlers.insert("compound",    new StartElementHandler(this,&TagFileParser::startCompound));
      m_startElementHandlers.insert("member",      new StartElementHandler(this,&TagFileParser::startMember));
      m_startElementHandlers.insert("name",        new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("base",        new StartElementHandler(this,&TagFileParser::startBase));
      m_startElementHandlers.insert("filename",    new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("includes",    new StartElementHandler(this,&TagFileParser::startIncludes));
      m_startElementHandlers.insert("path",        new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("anchorfile",  new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("anchor",      new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("arglist",     new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("title",       new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("subgroup",    new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("class",       new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("namespace",   new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("file",        new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("dir",         new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("page",        new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("docanchor",   new StartElementHandler(this,&TagFileParser::startDocAnchor));
      m_startElementHandlers.insert("tagfile",     new StartElementHandler(this,&TagFileParser::startIgnoreElement));
      m_startElementHandlers.insert("templarg",    new StartElementHandler(this,&TagFileParser::startStringValue));
      m_startElementHandlers.insert("type",        new StartElementHandler(this,&TagFileParser::startStringValue));

      m_endElementHandlers.insert("compound",    new EndElementHandler(this,&TagFileParser::endCompound));
      m_endElementHandlers.insert("member",      new EndElementHandler(this,&TagFileParser::endMember));
      m_endElementHandlers.insert("name",        new EndElementHandler(this,&TagFileParser::endName));
      m_endElementHandlers.insert("base",        new EndElementHandler(this,&TagFileParser::endBase));
      m_endElementHandlers.insert("filename",    new EndElementHandler(this,&TagFileParser::endFilename));
      m_endElementHandlers.insert("includes",    new EndElementHandler(this,&TagFileParser::endIncludes));
      m_endElementHandlers.insert("path",        new EndElementHandler(this,&TagFileParser::endPath));
      m_endElementHandlers.insert("anchorfile",  new EndElementHandler(this,&TagFileParser::endAnchorFile));
      m_endElementHandlers.insert("anchor",      new EndElementHandler(this,&TagFileParser::endAnchor));
      m_endElementHandlers.insert("arglist",     new EndElementHandler(this,&TagFileParser::endArglist));
      m_endElementHandlers.insert("title",       new EndElementHandler(this,&TagFileParser::endTitle));
      m_endElementHandlers.insert("subgroup",    new EndElementHandler(this,&TagFileParser::endSubgroup));
      m_endElementHandlers.insert("class"   ,    new EndElementHandler(this,&TagFileParser::endClass));
      m_endElementHandlers.insert("namespace",   new EndElementHandler(this,&TagFileParser::endNamespace));
      m_endElementHandlers.insert("file",        new EndElementHandler(this,&TagFileParser::endFile));
      m_endElementHandlers.insert("dir",         new EndElementHandler(this,&TagFileParser::endDir));
      m_endElementHandlers.insert("page",        new EndElementHandler(this,&TagFileParser::endPage));
      m_endElementHandlers.insert("docanchor",   new EndElementHandler(this,&TagFileParser::endDocAnchor));
      m_endElementHandlers.insert("tagfile",     new EndElementHandler(this,&TagFileParser::endIgnoreElement));
      m_endElementHandlers.insert("templarg",    new EndElementHandler(this,&TagFileParser::endTemplateArg));
      m_endElementHandlers.insert("type",        new EndElementHandler(this,&TagFileParser::endType));

      return TRUE;
    }

    bool startElement( const QString&, const QString&, 
                       const QString&name, const QXmlAttributes& attrib )
    {
      //printf("startElement `%s'\n",name.data());
      StartElementHandler *handler = m_startElementHandlers[name];
      if (handler)
      {
        (*handler)(attrib);
      }
      else 
      {
        warn("Warning: Unknown tag `%s' found!\n",name.data());
      }
      return TRUE;
    }

    bool endElement( const QString&, const QString&, const QString& name )
    {
      //printf("endElement `%s'\n",name.data());
      EndElementHandler *handler = m_endElementHandlers[name];
      if (handler)
      {
        (*handler)();
      }
      else 
      {
        warn("Warning: Unknown tag `%s' found!\n",name.data());
      }
      return TRUE;
    }

    bool characters ( const QString & ch ) 
    {
      m_curString+=ch;
      return TRUE;
    }

    void dump();
    void buildLists(Entry *root);
    void addIncludes();
    
  private:
    void buildMemberList(Entry *ce,QList<TagMemberInfo> &members);
    void addDocAnchors(Entry *e,const TagAnchorInfoList &l);
    QList<TagClassInfo>        m_tagFileClasses;
    QList<TagFileInfo>         m_tagFileFiles;
    QList<TagNamespaceInfo>    m_tagFileNamespaces;
    QList<TagGroupInfo>        m_tagFileGroups;
    QList<TagPageInfo>         m_tagFilePages;
    QList<TagPackageInfo>      m_tagFilePackages;
    QList<TagDirInfo>          m_tagFileDirs;
    QDict<StartElementHandler> m_startElementHandlers;
    QDict<EndElementHandler>   m_endElementHandlers;
    TagClassInfo              *m_curClass;
    TagFileInfo               *m_curFile;
    TagNamespaceInfo          *m_curNamespace;
    TagPackageInfo            *m_curPackage;
    TagGroupInfo              *m_curGroup;
    TagPageInfo               *m_curPage;
    TagDirInfo                *m_curDir;
    TagMemberInfo             *m_curMember;
    TagIncludeInfo            *m_curIncludes;
    QCString                   m_curString;
    QString                    m_tagName;
    QString                    m_fileName;
    State                      m_state;
    QStack<State>              m_stateStack;
    QXmlLocator               *m_locator;
    QString                    m_inputFileName;
};

/*! Error handler for the XML tag file parser. 
 *  Basically dumps all fatal error to stderr using err().
 */
class TagFileErrorHandler : public QXmlErrorHandler
{
  public:
    virtual ~TagFileErrorHandler() {}
    bool warning( const QXmlParseException & )
    {
      return FALSE;
    }
    bool error( const QXmlParseException & )
    {
      return FALSE;
    }
    bool fatalError( const QXmlParseException &exception )
    {
      err("Fatal error at line %d column %d: %s\n",
          exception.lineNumber(),exception.columnNumber(),
          exception.message().data());
      return FALSE;
    }
    QString errorString() { return ""; }

  private:
    QString errorMsg;
};

/*! Dumps the internal structures. For debugging only! */
void TagFileParser::dump()
{
  msg("Result:\n");
  QListIterator<TagClassInfo> lci(m_tagFileClasses);

  //============== CLASSES
  TagClassInfo *cd;
  for (;(cd=lci.current());++lci)
  {
    msg("class `%s'\n",cd->name.data());
    msg("  filename `%s'\n",cd->filename.data());
    if (cd->bases)
    {
      QListIterator<BaseInfo> bii(*cd->bases);
      BaseInfo *bi;
      for ( bii.toFirst() ; (bi=bii.current()) ; ++bii) 
      {
        msg( "  base: %s \n", bi->name.data() );
      }
    }

    QListIterator<TagMemberInfo> mci(cd->members);
    TagMemberInfo *md;
    for (;(md=mci.current());++mci)
    {
      msg("  member:\n");
      msg("    kind: `%s'\n",md->kind.data());
      msg("    name: `%s'\n",md->name.data());
      msg("    anchor: `%s'\n",md->anchor.data());
      msg("    arglist: `%s'\n",md->arglist.data());
    }
  }
  //============== NAMESPACES
  QListIterator<TagNamespaceInfo> lni(m_tagFileNamespaces);
  TagNamespaceInfo *nd;
  for (;(nd=lni.current());++lni)
  {
    msg("namespace `%s'\n",nd->name.data());
    msg("  filename `%s'\n",nd->filename.data());
    QStringList::Iterator it;
    for ( it = nd->classList.begin(); 
        it != nd->classList.end(); ++it ) 
    {
      msg( "  class: %s \n", (*it).latin1() );
    }

    QListIterator<TagMemberInfo> mci(nd->members);
    TagMemberInfo *md;
    for (;(md=mci.current());++mci)
    {
      msg("  member:\n");
      msg("    kind: `%s'\n",md->kind.data());
      msg("    name: `%s'\n",md->name.data());
      msg("    anchor: `%s'\n",md->anchor.data());
      msg("    arglist: `%s'\n",md->arglist.data());
    }
  }
  //============== FILES
  QListIterator<TagFileInfo> lfi(m_tagFileFiles);
  TagFileInfo *fd;
  for (;(fd=lfi.current());++lfi)
  {
    msg("file `%s'\n",fd->name.data());
    msg("  filename `%s'\n",fd->filename.data());
    QStringList::Iterator it;
    for ( it = fd->namespaceList.begin(); 
        it != fd->namespaceList.end(); ++it ) 
    {
      msg( "  namespace: %s \n", (*it).latin1() );
    }
    for ( it = fd->classList.begin(); 
        it != fd->classList.end(); ++it ) 
    {
      msg( "  class: %s \n", (*it).latin1() );
    }

    QListIterator<TagMemberInfo> mci(fd->members);
    TagMemberInfo *md;
    for (;(md=mci.current());++mci)
    {
      msg("  member:\n");
      msg("    kind: `%s'\n",md->kind.data());
      msg("    name: `%s'\n",md->name.data());
      msg("    anchor: `%s'\n",md->anchor.data());
      msg("    arglist: `%s'\n",md->arglist.data());
    }

    QListIterator<TagIncludeInfo> mii(fd->includes);
    TagIncludeInfo *ii;
    for (;(ii=mii.current());++mii)
    {
      msg("  includes id: %s name: %s\n",ii->id.data(),ii->name.data());
    }
  }

  //============== GROUPS
  QListIterator<TagGroupInfo> lgi(m_tagFileGroups);
  TagGroupInfo *gd;
  for (;(gd=lgi.current());++lgi)
  {
    msg("group `%s'\n",gd->name.data());
    msg("  filename `%s'\n",gd->filename.data());
    QStringList::Iterator it;
    for ( it = gd->namespaceList.begin(); 
        it != gd->namespaceList.end(); ++it ) 
    {
      msg( "  namespace: %s \n", (*it).latin1() );
    }
    for ( it = gd->classList.begin(); 
        it != gd->classList.end(); ++it ) 
    {
      msg( "  class: %s \n", (*it).latin1() );
    }
    for ( it = gd->fileList.begin(); 
        it != gd->fileList.end(); ++it ) 
    {
      msg( "  file: %s \n", (*it).latin1() );
    }
    for ( it = gd->subgroupList.begin(); 
        it != gd->subgroupList.end(); ++it ) 
    {
      msg( "  subgroup: %s \n", (*it).latin1() );
    }
    for ( it = gd->pageList.begin(); 
        it != gd->pageList.end(); ++it ) 
    {
      msg( "  page: %s \n", (*it).latin1() );
    }

    QListIterator<TagMemberInfo> mci(gd->members);
    TagMemberInfo *md;
    for (;(md=mci.current());++mci)
    {
      msg("  member:\n");
      msg("    kind: `%s'\n",md->kind.data());
      msg("    name: `%s'\n",md->name.data());
      msg("    anchor: `%s'\n",md->anchor.data());
      msg("    arglist: `%s'\n",md->arglist.data());
    }
  }
  //============== PAGES
  QListIterator<TagPageInfo> lpi(m_tagFilePages);
  TagPageInfo *pd;
  for (;(pd=lpi.current());++lpi)
  {
    msg("page `%s'\n",pd->name.data());
    msg("  title `%s'\n",pd->title.data());
    msg("  filename `%s'\n",pd->filename.data());
  }
  //============== DIRS
  QListIterator<TagDirInfo> ldi(m_tagFileDirs);
  TagDirInfo *dd;
  for (;(dd=ldi.current());++ldi)
  {
    msg("dir `%s'\n",dd->name.data());
    msg("  path `%s'\n",dd->path.data());
    QStringList::Iterator it;
    for ( it = dd->fileList.begin(); 
        it != dd->fileList.end(); ++it ) 
    {
      msg( "  file: %s \n", (*it).latin1() );
    }
    for ( it = dd->subdirList.begin(); 
        it != dd->subdirList.end(); ++it ) 
    {
      msg( "  subdir: %s \n", (*it).latin1() );
    }
  }
}

void TagFileParser::addDocAnchors(Entry *e,const TagAnchorInfoList &l)
{
  QListIterator<TagAnchorInfo> tli(l);
  TagAnchorInfo *ta;
  for (tli.toFirst();(ta=tli.current());++tli)
  {
    if (Doxygen::sectionDict.find(ta->label)==0)
    {
      //printf("New sectionInfo file=%s anchor=%s\n",
      //    ta->fileName.data(),ta->label.data());
      SectionInfo *si=new SectionInfo(ta->fileName,ta->label,ta->label,
          SectionInfo::Anchor,m_tagName);
      Doxygen::sectionDict.insert(ta->label,si);
      e->anchors->append(si);
    }
    else
    {
      warn("Duplicate anchor %s found\n",ta->label.data());
    }
  }
}

void TagFileParser::buildMemberList(Entry *ce,QList<TagMemberInfo> &members)
{
  QListIterator<TagMemberInfo> mii(members);
  TagMemberInfo *tmi;
  for (;(tmi=mii.current());++mii)
  {
    Entry *me      = new Entry;
    me->type       = tmi->type;
    me->name       = tmi->name;
    me->args       = tmi->arglist;
    if (!me->args.isEmpty())
    {
      delete me->argList;
      me->argList = new ArgumentList;
      stringToArgumentList(me->args,me->argList);
    }
    me->protection = tmi->prot;
    me->virt       = tmi->virt;
    me->stat       = tmi->isStatic;
    me->fileName   = ce->fileName;
    if (ce->section == Entry::GROUPDOC_SEC)
    {
      me->groups->append(new Grouping(ce->name,Grouping::GROUPING_INGROUP));
    }
    addDocAnchors(me,tmi->docAnchors);
    TagInfo *ti    = new TagInfo;
    ti->tagName    = m_tagName;
    ti->anchor     = tmi->anchor;
    ti->fileName   = tmi->anchorFile;
    me->tagInfo    = ti;
    if (tmi->kind=="define")
    {
      me->type="#define";
      me->section = Entry::DEFINE_SEC;
    }
    else if (tmi->kind=="enumvalue")
    {
      me->section = Entry::VARIABLE_SEC;
      me->mtype = Method;
    }
    else if (tmi->kind=="property")
    {
      me->section = Entry::VARIABLE_SEC;
      me->mtype = Property;
    }
    else if (tmi->kind=="event")
    {
      me->section = Entry::VARIABLE_SEC;
      me->mtype = Event;
    }
    else if (tmi->kind=="variable")
    {
      me->section = Entry::VARIABLE_SEC;
      me->mtype = Method;
    }
    else if (tmi->kind=="typedef")
    {
      me->section = Entry::VARIABLE_SEC; //Entry::TYPEDEF_SEC;
      me->type.prepend("typedef ");
      me->mtype = Method;
    }
    else if (tmi->kind=="enumeration")
    {
      me->section = Entry::ENUM_SEC;
      me->mtype = Method;
    }
    else if (tmi->kind=="function")
    {
      me->section = Entry::FUNCTION_SEC;
      me->mtype = Method;
    }
    else if (tmi->kind=="signal")
    {
      me->section = Entry::FUNCTION_SEC;
      me->mtype = Signal;
    }
    else if (tmi->kind=="prototype")
    {
      me->section = Entry::FUNCTION_SEC;
      me->mtype = Method;
    }
    else if (tmi->kind=="friend")
    {
      me->section = Entry::FUNCTION_SEC;
      me->type.prepend("friend ");
      me->mtype = Method;
    }
    else if (tmi->kind=="dcop")
    {
      me->section = Entry::FUNCTION_SEC;
      me->mtype = DCOP;
    }
    else if (tmi->kind=="slot")
    {
      me->section = Entry::FUNCTION_SEC;
      me->mtype = Slot;
    }
    ce->addSubEntry(me);
  }
}

static QString stripPath(const QString &s)
{
  int i=s.findRev('/');
  if (i!=-1)
  {
    return s.right(s.length()-i-1);
  }
  else
  {
    return s;
  }
}

/*! Injects the info gathered by the XML parser into the Entry tree.
 *  This tree contains the information extracted from the input in a 
 *  "unrelated" form.
 */
void TagFileParser::buildLists(Entry *root)
{
  // build class list
  TagClassInfo *tci = m_tagFileClasses.first();
  while (tci)
  {
    Entry *ce = new Entry;
    ce->section = Entry::CLASS_SEC;
    switch (tci->kind)
    {
      case TagClassInfo::Class:     break;
      case TagClassInfo::Struct:    ce->spec = Entry::Struct;    break;
      case TagClassInfo::Union:     ce->spec = Entry::Union;     break;
      case TagClassInfo::Interface: ce->spec = Entry::Interface; break;
      case TagClassInfo::Exception: ce->spec = Entry::Exception; break;
      case TagClassInfo::Protocol:  ce->spec = Entry::Protocol;  break;
      case TagClassInfo::Category:  ce->spec = Entry::Category;  break;
    }
    ce->name     = tci->name;
    if (tci->kind==TagClassInfo::Protocol) 
    {
      ce->name+="-p";
    }
    addDocAnchors(ce,tci->docAnchors);
    TagInfo *ti  = new TagInfo;
    ti->tagName  = m_tagName;
    ti->fileName = tci->filename;
    ce->tagInfo = ti;
    ce->objc = tci->isObjC;
    // transfer base class list
    if (tci->bases)
    {
      delete ce->extends;
      ce->extends = tci->bases; tci->bases = 0;
    }
    if (tci->templateArguments)
    {
      if (ce->tArgLists==0) 
      {
        ce->tArgLists = new QList<ArgumentList>;
        ce->tArgLists->setAutoDelete(TRUE);
      }
      ArgumentList *al = new ArgumentList;
      ce->tArgLists->append(al);
      
      QListIterator<QString> sli(*tci->templateArguments);
      QString *argName;
      for (;(argName=sli.current());++sli)
      {
        Argument *a = new Argument;
        a->type = "class";
        a->name = *argName;
        al->append(a);
      }
    }

    buildMemberList(ce,tci->members);
    root->addSubEntry(ce);
    tci = m_tagFileClasses.next();
  }

  // build file list
  TagFileInfo *tfi = m_tagFileFiles.first();
  while (tfi)
  {
    Entry *fe = new Entry;
    fe->section = guessSection(tfi->name);
    fe->name     = tfi->name;
    addDocAnchors(fe,tfi->docAnchors);
    TagInfo *ti  = new TagInfo;
    ti->tagName  = m_tagName;
    ti->fileName = tfi->filename;
    fe->tagInfo  = ti;
    
    QString fullName = m_tagName+":"+tfi->path+stripPath(tfi->name);
    fe->fileName = fullName;
    //printf("new FileDef() filename=%s\n",tfi->filename.data());
    FileDef *fd = new FileDef(m_tagName+":"+tfi->path,
                              tfi->name,m_tagName,
                              tfi->filename
                             );
    FileName *mn;
    if ((mn=Doxygen::inputNameDict->find(tfi->name)))
    {
      mn->append(fd);
    }
    else
    {
      mn = new FileName(fullName,tfi->name);
      mn->append(fd);
      Doxygen::inputNameList->inSort(mn);
      Doxygen::inputNameDict->insert(tfi->name,mn);
    }
    buildMemberList(fe,tfi->members);
    root->addSubEntry(fe);
    tfi = m_tagFileFiles.next();
  }

  // build namespace list
  TagNamespaceInfo *tni = m_tagFileNamespaces.first();
  while (tni)
  {
    Entry *ne    = new Entry;
    ne->section  = Entry::NAMESPACE_SEC;
    ne->name     = tni->name;
    addDocAnchors(ne,tni->docAnchors);
    TagInfo *ti  = new TagInfo;
    ti->tagName  = m_tagName;
    ti->fileName = tni->filename;
    ne->tagInfo  = ti;

    buildMemberList(ne,tni->members);
    root->addSubEntry(ne);
    tni = m_tagFileNamespaces.next();
  }

  // build package list
  TagPackageInfo *tpgi = m_tagFilePackages.first();
  while (tpgi)
  {
    Entry *pe    = new Entry;
    pe->section  = Entry::PACKAGE_SEC;
    pe->name     = tpgi->name;
    addDocAnchors(pe,tpgi->docAnchors);
    TagInfo *ti  = new TagInfo;
    ti->tagName  = m_tagName;
    ti->fileName = tpgi->filename;
    pe->tagInfo  = ti;

    buildMemberList(pe,tpgi->members);
    root->addSubEntry(pe);
    tpgi = m_tagFilePackages.next();
  }

  // build group list, but only if config file says to include it
  //if (Config_getBool("EXTERNAL_GROUPS")) 
  //{
    TagGroupInfo *tgi = m_tagFileGroups.first();
    while (tgi)
    {
      Entry *ge    = new Entry;
      ge->section  = Entry::GROUPDOC_SEC;
      ge->name     = tgi->name;
      ge->type     = tgi->title;
      addDocAnchors(ge,tgi->docAnchors);
      TagInfo *ti  = new TagInfo;
      ti->tagName  = m_tagName;
      ti->fileName = tgi->filename;
      ge->tagInfo  = ti;
      
      buildMemberList(ge,tgi->members);
      root->addSubEntry(ge);
      tgi = m_tagFileGroups.next();
    }
  //}

  // build page list
  TagPageInfo *tpi = m_tagFilePages.first();
  while (tpi)
  {
    Entry *pe    = new Entry;
    pe->section  = Entry::PAGEDOC_SEC;
    pe->name     = tpi->name;
    pe->args     = tpi->title;
    addDocAnchors(pe,tpi->docAnchors);
    TagInfo *ti  = new TagInfo;
    ti->tagName  = m_tagName;
    ti->fileName = tpi->filename;
    pe->tagInfo  = ti;

    root->addSubEntry(pe);
    tpi = m_tagFilePages.next();
  }
}

void TagFileParser::addIncludes()
{
  TagFileInfo *tfi = m_tagFileFiles.first();
  while (tfi)
  {
    //printf("tag file tagName=%s path=%s name=%s\n",m_tagName.data(),tfi->path.data(),tfi->name.data());
    FileName *fn = Doxygen::inputNameDict->find(tfi->name);
    if (fn)
    {
      //printf("found\n");
      FileNameIterator fni(*fn);
      FileDef *fd;
      for (;(fd=fni.current());++fni)
      {
        //printf("input file path=%s name=%s\n",fd->getPath().data(),fd->name().data());
        if (fd->getPath()==QCString(m_tagName+":"+tfi->path))
        {
          //printf("found\n");
          QListIterator<TagIncludeInfo> mii(tfi->includes);
          TagIncludeInfo *ii;
          for (;(ii=mii.current());++mii)
          {
            //printf("ii->name=`%s'\n",ii->name.data());
            FileName *ifn = Doxygen::inputNameDict->find(ii->name);
            ASSERT(ifn!=0);
            if (ifn)
            {
              FileNameIterator ifni(*ifn);
              FileDef *ifd;
              for (;(ifd=ifni.current());++ifni)
              {
                //printf("ifd->getOutputFileBase()=%s ii->id=%s\n",
                //        ifd->getOutputFileBase().data(),ii->id.data());
                if (ifd->getOutputFileBase()==QCString(ii->id))
                {
                  fd->addIncludeDependency(ifd,ii->text,ii->isLocal,ii->isImported);
                }
              }
            }
          }
        }
      } 
    }
    tfi = m_tagFileFiles.next();
  }
}

void parseTagFile(Entry *root,const char *fullName,const char *tagName)
{
  QFileInfo fi(fullName);
  if (!fi.exists()) return;
  TagFileParser handler( tagName );
  handler.setFileName(fullName);
  TagFileErrorHandler errorHandler;
  QFile xmlFile( fullName );
  QXmlInputSource source( xmlFile );
  QXmlSimpleReader reader;
  reader.setContentHandler( &handler );
  reader.setErrorHandler( &errorHandler );
  reader.parse( source );
  handler.buildLists(root);
  handler.addIncludes();
  //handler.dump();
}


