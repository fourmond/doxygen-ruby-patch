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

#ifndef FILEDEF_H
#define FILEDEF_H

#include "index.h"
#include <qlist.h>
#include <qintdict.h>
#include <qdict.h>
#include "config.h"
#include "definition.h"
#include "memberlist.h"
#include "util.h"

class FileDef;
class FileList;
class ClassSDict;
class ClassDef;
class ClassList;
class MemberDef;
class OutputList;
class NamespaceDef;
class NamespaceSDict;
class MemberGroupSDict;
class PackageDef;
class DirDef;

struct IncludeInfo
{
  IncludeInfo() { fileDef=0; local=FALSE; }
  ~IncludeInfo() {}
  FileDef *fileDef;
  QCString includeName;
  bool local;
  bool imported;
};

/*! \class FileDef filedef.h
    \brief A File definition.
    
    An object of this class contains all file information that is gathered.
    This includes the members and compounds defined in the file.
    
    The member writeDocumentation() can be used to generate the page of
    documentation to HTML and LaTeX.
*/

class FileDef : public Definition
{
  friend class FileName;

  public:
    //enum FileType { Source, Header, Unknown };

    FileDef(const char *p,const char *n,const char *ref=0,const char *dn=0);
   ~FileDef();
    DefType definitionType() const { return TypeFile; }

    /*! Returns the unique file name (this may include part of the path). */
    QCString name() const 
    { 
      if (Config_getBool("FULL_PATH_NAMES")) 
        return filename; 
      else 
        return Definition::name(); 
    } 

    QCString fileName() const
    {
      return filename;
    }
    
    QCString getOutputFileBase() const 
    { return convertNameToFile(diskname); }

    QCString getFileBase() const
    { return diskname; }

    QCString getSourceFileBase() const;
    
    /*! Returns the name of the verbatim copy of this file (if any). */
    QCString includeName() const;
    
    /*! Returns the absolute path including the file name. */
    QCString absFilePath() const { return filepath; }
    
    
    /*! Returns the name as it is used in the documentation */
    QCString docName() const { return docname; }
    
    void addSourceRef(int line,Definition *d,MemberDef *md);
    Definition *getSourceDefinition(int lineNr);
    MemberDef *getSourceMember(int lineNr);

    /* Sets the name of the include file to \a n. */
    //void setIncludeName(const char *n_) { incName=n_; }
    
    /*! Returns the absolute path of this file. */ 
    QCString getPath() const { return path; }

    /*! Returns version of this file. */
    QCString getVersion() const { return fileVersion; }
    
    bool isLinkableInProject() const;

    bool isLinkable() const
    {
      return isLinkableInProject() || isReference();
    }
    bool isIncluded(const QCString &name) const;

    bool isJava() const { return m_isJava; }
    bool isCSharp() const { return m_isCSharp; }

    void writeDocumentation(OutputList &ol);
    void writeMemberPages(OutputList &ol);
    void writeQuickMemberLinks(OutputList &ol,MemberDef *currentMd) const;
    void writeSummaryLinks(OutputList &ol);

    void writeSource(OutputList &ol);
    void parseSource();
    friend void generatedFileNames();
    void insertMember(MemberDef *md);
    void insertClass(ClassDef *cd);
    void insertNamespace(NamespaceDef *nd);
    void computeAnchors();

    void setPackageDef(PackageDef *pd) { package=pd; }
    PackageDef *packageDef() const { return package; }
    
    void setDirDef(DirDef *dd) { dir=dd; }
    DirDef *getDirDef() const { return dir; }

    void addUsingDirective(NamespaceDef *nd);
    NamespaceSDict *getUsedNamespaces() const;
    void addUsingDeclaration(Definition *def);
    SDict<Definition> *getUsedClasses() const { return usingDeclList; }
    void combineUsingRelations();

    bool generateSourceFile() const;
    void sortMemberLists();

    void addIncludeDependency(FileDef *fd,const char *incName,bool local,bool imported);
    void addIncludedByDependency(FileDef *fd,const char *incName,bool local,bool imported);
    QList<IncludeInfo> *includeFileList() const { return includeList; }
    QList<IncludeInfo> *includedByFileList() const { return includedByList; }

    void addMembersToMemberGroup();
    void distributeMemberGroupDocumentation();
    void findSectionsInDocumentation();
    void addIncludedUsingDirectives();

    void addListReferences();
    bool isDocumentationFile() const;
    bool includes(FileDef *incFile,QDict<FileDef> *includedFiles) const;

    MemberList *getMemberList(MemberList::ListType lt) const;
    const QList<MemberList> &getMemberLists() const { return m_memberLists; }

    /* user defined member groups */
    MemberGroupSDict *getMemberGroupSDict() const { return memberGroupSDict; }
    NamespaceSDict *getNamespaceSDict() const     { return namespaceSDict; }
    ClassSDict *getClassSDict() const             { return classSDict; }
    
    bool visited;

  protected:
    /**
     * Retrieves the file version from version control system.
     */
    void acquireFileVersion();

  private: 
    MemberList *createMemberList(MemberList::ListType lt);
    void addMemberToList(MemberList::ListType lt,MemberDef *md);
    void writeMemberDeclarations(OutputList &ol,MemberList::ListType lt,const QCString &title);
    void writeMemberDocumentation(OutputList &ol,MemberList::ListType lt,const QCString &title);
    void writeIncludeFiles(OutputList &ol);
    void writeIncludeGraph(OutputList &ol);
    void writeIncludedByGraph(OutputList &ol);
    void writeMemberGroups(OutputList &ol);
    void writeAuthorSection(OutputList &ol);
    void writeSourceLink(OutputList &ol);
    void writeNamespaceDeclarations(OutputList &ol,const QCString &title);
    void writeClassDeclarations(OutputList &ol,const QCString &title);
    void startMemberDeclarations(OutputList &ol);
    void endMemberDeclarations(OutputList &ol);
    void startMemberDocumentation(OutputList &ol);
    void endMemberDocumentation(OutputList &ol);
    void writeDetailedDescription(OutputList &ol,const QCString &title);
    void writeBriefDescription(OutputList &ol);

    QDict<IncludeInfo>   *includeDict;
    QList<IncludeInfo>   *includeList;
    QDict<IncludeInfo>   *includedByDict;
    QList<IncludeInfo>   *includedByList;
    NamespaceSDict       *usingDirList;
    SDict<Definition>    *usingDeclList;
    QCString              path;
    QCString              filepath;
    QCString              diskname;
    QCString              filename;
    QCString              docname;
    QIntDict<Definition> *srcDefDict;
    QIntDict<MemberDef>  *srcMemberDict;
    bool                  isSource;
    bool                  m_isJava;
    bool                  m_isCSharp;
    QCString              fileVersion;
    PackageDef           *package;
    DirDef               *dir;
    QList<MemberList>     m_memberLists;
    MemberGroupSDict     *memberGroupSDict;
    NamespaceSDict       *namespaceSDict;
    ClassSDict           *classSDict;
    bool                  m_subGrouping;
};


class FileList : public QList<FileDef>
{
  public:
    FileList() : m_pathName("tmp") {}
    FileList(const char *path) : QList<FileDef>(), m_pathName(path) {}
   ~FileList() {}
    QCString path() const { return m_pathName; }
    int compareItems(GCI item1,GCI item2)
    {
      FileDef *md1 = (FileDef *)item1;
      FileDef *md2 = (FileDef *)item2;
      return stricmp(md1->name(),md2->name());
    }
  private:
    QCString m_pathName;
};

class OutputNameList : public QList<FileList>
{
  public:
    OutputNameList() : QList<FileList>() {}
   ~OutputNameList() {}
    int compareItems(GCI item1,GCI item2)
    {
      FileList *fl1 = (FileList *)item1;
      FileList *fl2 = (FileList *)item2;
      return stricmp(fl1->path(),fl2->path());
    }
};

class OutputNameDict : public QDict<FileList>
{
  public:
    OutputNameDict(int size) : QDict<FileList>(size) {}
   ~OutputNameDict() {}
};

class Directory;

class DirEntry
{
  public:
    enum EntryKind { Dir, File };
    DirEntry(DirEntry *parent,FileDef *fd)  
       : m_parent(parent), m_name(fd->name()), m_kind(File), m_fd(fd), 
         m_isLast(FALSE) { }
    DirEntry(DirEntry *parent,QCString name)              
       : m_parent(parent), m_name(name), m_kind(Dir), 
         m_fd(0), m_isLast(FALSE) { }
    virtual ~DirEntry() { }
    EntryKind kind() const { return m_kind; }
    FileDef *file()  const { return m_fd; }
    bool isLast() const    { return m_isLast; }
    void setLast(bool b)   { m_isLast=b; }
    DirEntry *parent() const { return m_parent; }
    QCString name() const  { return m_name; }
    QCString path() const  { return parent() ? parent()->path()+"/"+name() : name(); }

  protected:
    DirEntry *m_parent;
    QCString m_name;

  private:
    EntryKind m_kind;
    FileDef   *m_fd;
    int num;
    bool m_isLast;
};

class Directory : public DirEntry
{
  public:
    Directory(Directory *parent,const QCString &name) 
       : DirEntry(parent,name)
    { m_children.setAutoDelete(TRUE); }
    virtual ~Directory()              {}
    void addChild(DirEntry *d)        { m_children.append(d); d->setLast(TRUE); }
    QList<DirEntry> &children()       { return m_children; }
    void rename(const QCString &name) { m_name=name; }
    void reParent(Directory *parent)  { m_parent=parent; }

  private:
    QList<DirEntry> m_children;
};

//void generateFileTree(QTextStream &t);
void generateFileTree();

#endif

