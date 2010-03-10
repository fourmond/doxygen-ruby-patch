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

#ifndef _DOT_H
#define _DOT_H

#include "qtbc.h"
#include <qlist.h>
#include <qdict.h>
#include "sortdict.h"

class ClassDef;
class FileDef;
class QTextStream;
class DotNodeList;
class ClassSDict;
class MemberDef;
class Definition;
class DirDef;
class GroupDef;
class DotGroupCollaboration;

enum GraphOutputFormat { BITMAP , EPS };

/** @brief Attributes of an edge of a dot graph */
struct EdgeInfo
{
  enum Colors { Blue=0, Green=1, Red=2, Purple=3, Grey=4, Orange=5 };
  enum Styles { Solid=0, Dashed=1 };
  EdgeInfo() : m_color(0), m_style(0), m_labColor(0) {}
 ~EdgeInfo() {}
  int m_color;
  int m_style;
  QCString m_label;
  QCString m_url;
  int m_labColor;
};

/** @brief A node in a dot graph */
class DotNode
{
  public:
    enum GraphType { Dependency, Inheritance, Collaboration, Hierarchy, CallGraph };
    enum TruncState { Unknown, Truncated, Untruncated };
    DotNode(int n,const char *lab,const char *tip,const char *url,
            bool rootNode=FALSE,ClassDef *cd=0);
   ~DotNode();
    void addChild(DotNode *n,
                  int edgeColor=EdgeInfo::Purple,
                  int edgeStyle=EdgeInfo::Solid,
                  const char *edgeLab=0,
                  const char *edgeURL=0,
                  int edgeLabCol=-1
                 );
    void addParent(DotNode *n);
    void deleteNode(DotNodeList &deletedList,SDict<DotNode> *skipNodes=0);
    void removeChild(DotNode *n);
    void removeParent(DotNode *n);
    int findParent( DotNode *n );
    void write(QTextStream &t,GraphType gt,GraphOutputFormat f,
               bool topDown,bool toChildren,bool backArrows,bool reNumber);
    int  m_subgraphId;
    void clearWriteFlag();
    void writeXML(QTextStream &t,bool isClassGraph);
    void writeDEF(QTextStream &t);
    QCString label() const { return m_label; }
    int  number() const { return m_number; }
    bool isVisible() const { return m_visible; }
    TruncState isTruncated() const { return m_truncated; }
    int distance() const { return m_distance; }

  private:
    void colorConnectedNodes(int curColor);
    void writeBox(QTextStream &t,GraphType gt,GraphOutputFormat f,
                  bool hasNonReachableChildren, bool reNumber=FALSE);
    void writeArrow(QTextStream &t,GraphType gt,GraphOutputFormat f,DotNode *cn,
                    EdgeInfo *ei,bool topDown, bool pointBack=TRUE, bool reNumber=FALSE);
    void setDistance(int distance);
    const DotNode   *findDocNode() const; // only works for acyclic graphs!
    void markAsVisible(bool b=TRUE) { m_visible=b; }
    void markAsTruncated(bool b=TRUE) { m_truncated=b ? Truncated : Untruncated; }
    int              m_number;
    QCString         m_label;     //!< label text
    QCString         m_tooltip;   //!< node's tooltip
    QCString         m_url;       //!< url of the node (format: remote$local)
    QList<DotNode>  *m_parents;   //!< list of parent nodes (incoming arrows)
    QList<DotNode>  *m_children;  //!< list of child nodes (outgoing arrows)
    QList<EdgeInfo> *m_edgeInfo;  //!< edge info for each child
    bool             m_deleted;   //!< used to mark a node as deleted
    bool             m_written;   //!< used to mark a node as written
    bool             m_hasDoc;    //!< used to mark a node as documented
    bool             m_isRoot;    //!< indicates if this is a root node
    ClassDef *       m_classDef;  //!< class representing this node (can be 0)
    bool             m_visible;   //!< is the node visible in the output
    TruncState       m_truncated; //!< does the node have non-visible children/parents
    int              m_distance;  //!< shortest path to the root node

    friend class DotGfxHierarchyTable;
    friend class DotClassGraph;
    friend class DotInclDepGraph;
    friend class DotNodeList;
    friend class DotCallGraph;
    friend class DotGroupCollaboration;

    friend QCString computeMd5Signature(
                      DotNode *root, GraphType gt,
                      GraphOutputFormat f, 
                      bool lrRank, bool renderParents,
                      bool backArrows,
                      QCString &graphStr
                     );
};

inline int DotNode::findParent( DotNode *n )
{
    if( !m_parents )
        return -1;
    return m_parents->find(n);
}

/** @brief Represents a graphical class hierarchy */
class DotGfxHierarchyTable
{
  public:
    DotGfxHierarchyTable();
   ~DotGfxHierarchyTable();
    void writeGraph(QTextStream &t,const char *path) const;
  
  private:
    void addHierarchy(DotNode *n,ClassDef *cd,bool hide);
    void addClassList(ClassSDict *cl);

    QList<DotNode> *m_rootNodes; 
    QDict<DotNode> *m_usedNodes; 
    static int      m_curNodeNumber;
    DotNodeList    *m_rootSubgraphs;
};

/** @brief Representation of a class inheritance or dependency graph */
class DotClassGraph
{
  public:
    DotClassGraph(ClassDef *cd,DotNode::GraphType t);
   ~DotClassGraph();
    bool isTrivial() const;
    bool isTooBig() const;
    QCString writeGraph(QTextStream &t,GraphOutputFormat f,const char *path,
                    const char *relPath, bool TBRank=TRUE,bool imageMap=TRUE) const;

    void writeXML(QTextStream &t);
    void writeDEF(QTextStream &t);
    QCString diskName() const;

  private:
    void buildGraph(ClassDef *cd,DotNode *n,bool base,int distance);
    bool determineVisibleNodes(DotNode *rootNode,int maxNodes,bool includeParents);
    void determineTruncatedNodes(QList<DotNode> &queue,bool includeParents);
    void addClass(ClassDef *cd,DotNode *n,int prot,const char *label,
                  const char *usedName,const char *templSpec,
                  bool base,int distance);

    DotNode        *   m_startNode;
    QDict<DotNode> *   m_usedNodes;
    static int         m_curNodeNumber;
    DotNode::GraphType m_graphType;
    QCString           m_diskName;
    bool               m_lrRank;
};

/** @brief Representation of an include dependency graph */
class DotInclDepGraph
{
  public:
    DotInclDepGraph(FileDef *fd,bool inverse);
   ~DotInclDepGraph();
    QCString writeGraph(QTextStream &t, GraphOutputFormat f,const char *path,
                    const char *relPath,
                    bool writeImageMap=TRUE) const;
    bool isTrivial() const;
    bool isTooBig() const;
    QCString diskName() const;
    void writeXML(QTextStream &t);

  private:
    void buildGraph(DotNode *n,FileDef *fd,int distance);
    void determineVisibleNodes(QList<DotNode> &queue,int &maxNodes);
    void determineTruncatedNodes(QList<DotNode> &queue);

    DotNode        *m_startNode;
    QDict<DotNode> *m_usedNodes;
    static int      m_curNodeNumber;
    QCString        m_diskName;
    int             m_maxDistance;
    bool            m_inverse;
};

/** @brief Representation of an call graph */
class DotCallGraph
{
  public:
    DotCallGraph(MemberDef *md,bool inverse);
   ~DotCallGraph();
    QCString writeGraph(QTextStream &t, GraphOutputFormat f,
                        const char *path,const char *relPath,bool writeImageMap=TRUE) const;
    void buildGraph(DotNode *n,MemberDef *md,int distance);
    bool isTrivial() const;
    bool isTooBig() const;
    void determineVisibleNodes(QList<DotNode> &queue, int &maxNodes);
    void determineTruncatedNodes(QList<DotNode> &queue);
    
  private:
    DotNode        *m_startNode;
    static int      m_curNodeNumber;
    QDict<DotNode> *m_usedNodes;
    int             m_maxDistance;
    int             m_recDepth;
    bool            m_inverse;
    QCString        m_diskName;
    Definition *    m_scope;
};

/** @brief Representation of an directory dependency graph */
class DotDirDeps
{
  public:
    DotDirDeps(DirDef *dir);
   ~DotDirDeps();
    bool isTrivial() const;
    QCString writeGraph(QTextStream &out,
                        GraphOutputFormat format,
                        const char *path,
                        const char *relPath,
                        bool writeImageMap=TRUE) const;
  private:
    DirDef *m_dir;
};

/** @brief Representation of a group collaboration graph */
class DotGroupCollaboration
{
  public :
    enum EdgeType 
    {  tmember = 0,
       tclass,
       tnamespace,
       tfile,
       tpages,
       tdir,
       thierarchy 
    };

    class Link
    {
      public:
        Link(const QCString lab,const QCString &u) : label(lab), url(u) {}
        QCString label;
        QCString url;
    };

    class Edge
    {
      public :
        Edge(DotNode *start,DotNode *end,EdgeType type) 
          : pNStart(start), pNEnd(end), eType(type)
        { links.setAutoDelete(TRUE); }

        DotNode* pNStart;
        DotNode* pNEnd;
        EdgeType eType;

        QList<Link> links;
        void write( QTextStream &t ) const;
    };

    DotGroupCollaboration(GroupDef* gd);
    ~DotGroupCollaboration();
    QCString writeGraph(QTextStream &t, GraphOutputFormat format,
                    const char *path,const char *relPath,
                    bool writeImageMap=TRUE) const;
    void buildGraph(GroupDef* gd);
    bool isTrivial() const;
  private :
    void addCollaborationMember( Definition* def, QCString& url, EdgeType eType );
    void addMemberList( class MemberList* ml );
    void writeGraphHeader(QTextStream &t) const;
    Edge* addEdge( DotNode* _pNStart, DotNode* _pNEnd, EdgeType _eType,
                   const QCString& _label, const QCString& _url );

    DotNode        *m_rootNode;
    int             m_curNodeId;
    QDict<DotNode> *m_usedNodes;
    QCString        m_diskName;
    QList<Edge>     m_edges;
};

/** @brief Helper class to run dot from doxygen.
 */
class DotRunner
{
  public:
    /** Creates a runner for a dot \a file. */
    DotRunner(const char *file);

    /** Adds an additional job to the run.
     *  Performing multiple jobs one file can be faster.
     */
    void addJob(const char *format,const char *output);

    void addPostProcessing(const char *cmd,const char *args);

    /** Runs dot for all jobs added. */
    bool run();
  private:
    QList<QCString> m_jobs;
    QCString m_postArgs;
    QCString m_postCmd;
    QCString m_file;
};


/** Generated a graphs legend page */
void generateGraphLegend(const char *path);

void writeDotGraphFromFile(const char *inFile,const char *outDir,
                           const char *outFile,GraphOutputFormat format);
QString getDotImageMapFromFile(const QString& inFile, const QString& outDir,
                               const QCString& relPath,const QString &context);

void writeDotDirDepGraph(QTextStream &t,DirDef *dd);

#endif
